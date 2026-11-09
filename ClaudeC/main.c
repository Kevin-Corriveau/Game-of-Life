/*
 * Conway's Game of Life - HashLife on an infinite, non-wrapping grid.
 * Windows + SDL3.
 *
 * Build (MSVC):   cl /O2 /I<SDL3>\include life.c /link /LIBPATH:<SDL3>\lib\x64 SDL3.lib
 * Build (MinGW):  gcc -O2 life.c -o life.exe -I<SDL3>/include -L<SDL3>/lib -lSDL3
 *
 * Run:            life pattern.txt          (pattern file format:  3;101100010)
 *
 * Controls
 *   Left/Middle/Right drag   pan
 *   Mouse wheel              zoom (around cursor)
 *   N / Right arrow          advance exactly ONE generation (memoized)
 *   J                        HashLife jump: advance 2^(k-3) generations in one go
 *   Space                    start / stop auto-run
 *   M                        auto-run uses single steps  <->  jumps
 *   Up / Down                faster / slower auto-run
 *   Esc                      quit
 *
 * Quadtree design
 *   - Nodes live in one growing array ("node list") on a 2 GB reserve-then-commit
 *     stack. A node is 4 child indices + 2 memoized results; nodes know no depth.
 *   - Indices [0, NUM_CANON) are the canonical leaf nodes (LEAF_SIZE x LEAF_SIZE
 *     cells, 4x4 by default). Index == bit pattern, so index range reveals depth.
 *     Those list slots hold "null" nodes (all zeros); the real cell bits live in
 *     the separate fixed array canon[].
 *   - Every other node is appended in creation order. A node's depth is implied
 *     by its children; the root's depth is tracked separately (U.level).
 *   - A separate hash map (on its own stack allocator, linear probing, doubles at
 *     75% load) maps child-quadruple -> node index so identical nodes are shared.
 *   - Nodes are immutable. Every change builds new nodes and moves the root.
 */

#define WIN32_LEAN_AND_MEAN
#define NOMINMAX
#include <windows.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdarg.h>
#include <ctype.h>
#include <math.h>

typedef uint8_t  u8;
typedef uint16_t u16;
typedef uint32_t u32;
typedef uint64_t u64;
typedef int64_t  i64;

/* ------------------------------------------------------------------------- */
/* Configuration                                                             */
/* ------------------------------------------------------------------------- */

/* log2 of the canonical leaf edge. 2 -> 4x4 leaves (65536 canonical nodes).
 * 1 -> 2x2 leaves also works. 3 (8x8) is impossible: 2^64 canonical nodes. */
#ifndef LEAF_LOG
#define LEAF_LOG 2
#endif
#define LEAF_SIZE   (1 << LEAF_LOG)
#define LEAF_CELLS  (LEAF_SIZE * LEAF_SIZE)
#define NUM_CANON   (1u << LEAF_CELLS)

typedef char leaf_cells_must_fit_in_u16[(LEAF_CELLS <= 16) ? 1 : -1];

/* The smallest non-canonical node: 4 canonical leaves, e.g. 8x8 cells. */
#define BASE_LEVEL      (LEAF_LOG + 1)
#define BASE_SIZE       (1 << BASE_LEVEL)
/* Generations a BASE_LEVEL node advances for its "full" result: 2^(level-2). */
#define BASE_GENS       (1 << (LEAF_LOG - 1))
#define MIN_ROOT_LEVEL  (LEAF_LOG + 2)
#define MAX_LEVEL       60

#define NONE            0xFFFFFFFFu

#define STACK_RESERVE   ((size_t)2 << 30)     /* 2 GB of address space each   */
#define COMMIT_CHUNK    ((size_t)4 << 20)     /* commit granularity: 4 MB     */

/* ------------------------------------------------------------------------- */
/* Fatal errors                                                              */
/* ------------------------------------------------------------------------- */

static void fatal(const char *fmt, ...)
{
    char msg[512];
    va_list ap;
    va_start(ap, fmt);
    vsnprintf(msg, sizeof msg, fmt, ap);
    va_end(ap);
    fprintf(stderr, "fatal: %s\n", msg);
    MessageBoxA(NULL, msg, "Game of Life", MB_OK | MB_ICONERROR);
    ExitProcess(1);
}

/* ------------------------------------------------------------------------- */
/* Stack allocator: reserve virtual memory up front, commit as it grows      */
/* ------------------------------------------------------------------------- */

typedef struct {
    u8    *base;
    size_t reserved, committed, used;
} Stack;

static void stack_init(Stack *s, size_t reserve)
{
    s->base = (u8 *)VirtualAlloc(NULL, reserve, MEM_RESERVE, PAGE_NOACCESS);
    if (!s->base) fatal("Out of memory: could not reserve %zu MB of address space", reserve >> 20);
    s->reserved = reserve;
    s->committed = 0;
    s->used = 0;
}

static void *stack_push(Stack *s, size_t bytes, size_t align)
{
    size_t start = (s->used + (align - 1)) & ~(align - 1);
    if (bytes > s->reserved || start > s->reserved - bytes)
        fatal("Out of memory: %zu MB stack exhausted", s->reserved >> 20);
    size_t end = start + bytes;
    if (end > s->committed) {
        size_t nc = (end + COMMIT_CHUNK - 1) & ~(COMMIT_CHUNK - 1);
        if (nc > s->reserved) nc = s->reserved;
        if (!VirtualAlloc(s->base + s->committed, nc - s->committed, MEM_COMMIT, PAGE_READWRITE))
            fatal("Out of memory: could not commit more memory (%zu MB in use)", s->committed >> 20);
        s->committed = nc;
    }
    s->used = end;
    return s->base + start;
}

static void stack_pop_to(Stack *s, size_t mark)
{
    s->used = mark;
    size_t keep = (mark + COMMIT_CHUNK - 1) & ~(COMMIT_CHUNK - 1);
    if (keep < s->committed) {
        VirtualFree(s->base + keep, s->committed - keep, MEM_DECOMMIT);
        s->committed = keep;
    }
}

/* ------------------------------------------------------------------------- */
/* Node storage                                                              */
/* ------------------------------------------------------------------------- */

/* child order: 0 = NW, 1 = NE, 2 = SW, 3 = SE */
typedef struct {
    u32 child[4];
    u32 result;   /* center half after 2^(level-2) generations, or NONE        */
    u32 step;     /* center half after exactly 1 generation, or NONE           */
} Node;

/* Canonical leaves, kept in their own fixed array (bit y*LEAF_SIZE+x). */
typedef struct { u16 cells; } CanonNode;
static CanonNode canon[NUM_CANON];

static Stack  node_stack;
static Node  *nodes;          /* == node_stack.base, never moves */
static u32    node_count;

static Stack  map_stack;
static u32   *map_slots;      /* 0 = empty (canonical index 0 is never stored) */
static u64    map_cap, map_count;

static void storage_init(void)
{
    stack_init(&node_stack, STACK_RESERVE);
    nodes = (Node *)stack_push(&node_stack, (size_t)NUM_CANON * sizeof(Node), 1);
    memset(nodes, 0, (size_t)NUM_CANON * sizeof(Node));      /* the "null" nodes */
    node_count = NUM_CANON;
    for (u32 i = 0; i < NUM_CANON; i++) canon[i].cells = (u16)i;

    stack_init(&map_stack, STACK_RESERVE);
    map_cap = 1u << 16;
    map_count = 0;
    map_slots = (u32 *)stack_push(&map_stack, map_cap * sizeof(u32), 16);
    memset(map_slots, 0, map_cap * sizeof(u32));
}

static inline u64 hash4(u32 a, u32 b, u32 c, u32 d)
{
    u64 h = (u64)a * 0x9E3779B97F4A7C15ull;
    h ^= h >> 32; h = (h + b) * 0xC2B2AE3D27D4EB4Full;
    h ^= h >> 29; h = (h + c) * 0x165667B19E3779F9ull;
    h ^= h >> 32; h = (h + d) * 0x9E3779B97F4A7C15ull;
    h ^= h >> 31;
    return h;
}

static void map_grow(void)
{
    u64 ncap = map_cap * 2;
    u32 *old = map_slots;
    u32 *nt = (u32 *)stack_push(&map_stack, ncap * sizeof(u32), 16);   /* above old */
    memset(nt, 0, ncap * sizeof(u32));
    u64 mask = ncap - 1;
    for (u64 i = 0; i < map_cap; i++) {
        u32 e = old[i];
        if (!e) continue;
        const Node *n = &nodes[e];
        u64 h = hash4(n->child[0], n->child[1], n->child[2], n->child[3]) & mask;
        while (nt[h]) h = (h + 1) & mask;
        nt[h] = e;
    }
    /* slide the new table down to the start of the stack and give the rest back */
    memmove(old, nt, ncap * sizeof(u32));
    map_cap = ncap;
    stack_pop_to(&map_stack, ncap * sizeof(u32));
}

/* Find or create the (immutable, shared) node with these four children. */
static u32 get_node(u32 nw, u32 ne, u32 sw, u32 se)
{
    u64 mask = map_cap - 1;
    u64 h = hash4(nw, ne, sw, se) & mask;
    for (;;) {
        u32 e = map_slots[h];
        if (!e) break;
        const Node *n = &nodes[e];
        if (n->child[0] == nw && n->child[1] == ne && n->child[2] == sw && n->child[3] == se)
            return e;
        h = (h + 1) & mask;
    }
    if ((map_count + 1) * 4 > map_cap * 3) {
        map_grow();
        mask = map_cap - 1;
        h = hash4(nw, ne, sw, se) & mask;
        while (map_slots[h]) h = (h + 1) & mask;
    }
    if (node_count >= NONE - 1) fatal("Out of memory: node index space exhausted");
    Node *n = (Node *)stack_push(&node_stack, sizeof(Node), 1);
    n->child[0] = nw; n->child[1] = ne; n->child[2] = sw; n->child[3] = se;
    n->result = NONE;
    n->step = NONE;
    u32 idx = node_count++;
    map_slots[h] = idx;
    map_count++;
    return idx;
}

/* ------------------------------------------------------------------------- */
/* Leaf-level (brute force) helpers                                          */
/* ------------------------------------------------------------------------- */

static u32 empty_cache[MAX_LEVEL + 2];

/* The empty node of a given level. Level LEAF_LOG is canonical index 0. */
static u32 empty_node(int level)
{
    if (level <= LEAF_LOG) return 0;
    if (!empty_cache[level]) {
        u32 e = empty_node(level - 1);
        empty_cache[level] = get_node(e, e, e, e);
    }
    return empty_cache[level];
}

static void unpack_base(u32 idx, u8 g[BASE_SIZE][BASE_SIZE])
{
    const Node *n = &nodes[idx];
    for (int q = 0; q < 4; q++) {
        u16 bits = canon[n->child[q]].cells;
        int ox = (q & 1) * LEAF_SIZE, oy = (q >> 1) * LEAF_SIZE;
        for (int cy = 0; cy < LEAF_SIZE; cy++)
            for (int cx = 0; cx < LEAF_SIZE; cx++)
                g[oy + cy][ox + cx] = (bits >> (cy * LEAF_SIZE + cx)) & 1;
    }
}

/* Canonical leaves are enumerated by bit pattern, so index == pattern. */
static u32 pack_center(u8 g[BASE_SIZE][BASE_SIZE])
{
    u32 bits = 0;
    int off = LEAF_SIZE / 2;
    for (int cy = 0; cy < LEAF_SIZE; cy++)
        for (int cx = 0; cx < LEAF_SIZE; cx++)
            if (g[off + cy][off + cx]) bits |= 1u << (cy * LEAF_SIZE + cx);
    return bits;
}

static void life_grid(u8 g[BASE_SIZE][BASE_SIZE], int gens)
{
    u8 t[BASE_SIZE][BASE_SIZE];
    while (gens-- > 0) {
        for (int y = 0; y < BASE_SIZE; y++)
            for (int x = 0; x < BASE_SIZE; x++) {
                int c = 0;
                for (int dy = -1; dy <= 1; dy++)
                    for (int dx = -1; dx <= 1; dx++) {
                        if (!dx && !dy) continue;
                        int xx = x + dx, yy = y + dy;
                        if (xx >= 0 && yy >= 0 && xx < BASE_SIZE && yy < BASE_SIZE) c += g[yy][xx];
                    }
                t[y][x] = (c == 3) || (c == 2 && g[y][x]);
            }
        memcpy(g, t, sizeof t);
    }
}

/* Center LEAF_SIZE x LEAF_SIZE of a BASE_LEVEL node after `gens` generations. */
static u32 base_advance(u32 idx, int gens)
{
    u8 g[BASE_SIZE][BASE_SIZE];
    unpack_base(idx, g);
    life_grid(g, gens);
    return pack_center(g);
}

/* ------------------------------------------------------------------------- */
/* HashLife                                                                  */
/* ------------------------------------------------------------------------- */

/* Center half of a node of the given level (level >= BASE_LEVEL), no time passes. */
static u32 center(u32 idx, int level)
{
    if (level == BASE_LEVEL) {
        u8 g[BASE_SIZE][BASE_SIZE];
        unpack_base(idx, g);
        return pack_center(g);
    }
    const Node *n = &nodes[idx];
    return get_node(nodes[n->child[0]].child[3], nodes[n->child[1]].child[2],
                    nodes[n->child[2]].child[1], nodes[n->child[3]].child[0]);
}

/* The 3x3 overlapping sub-nodes (one level down) of a node with level > BASE_LEVEL. */
static void nine(u32 idx, u32 n[9])
{
    const Node *p = &nodes[idx];
    u32 a = p->child[0], b = p->child[1], c = p->child[2], d = p->child[3];
    const Node *A = &nodes[a], *B = &nodes[b], *C = &nodes[c], *D = &nodes[d];
    n[0] = a;
    n[1] = get_node(A->child[1], B->child[0], A->child[3], B->child[2]);
    n[2] = b;
    n[3] = get_node(A->child[2], A->child[3], C->child[0], C->child[1]);
    n[4] = get_node(A->child[3], B->child[2], C->child[1], D->child[0]);
    n[5] = get_node(B->child[2], B->child[3], D->child[0], D->child[1]);
    n[6] = c;
    n[7] = get_node(C->child[1], D->child[0], C->child[3], D->child[2]);
    n[8] = d;
}

static void quarters(const u32 r[9], u32 q[4])
{
    q[0] = get_node(r[0], r[1], r[3], r[4]);
    q[1] = get_node(r[1], r[2], r[4], r[5]);
    q[2] = get_node(r[3], r[4], r[6], r[7]);
    q[3] = get_node(r[4], r[5], r[7], r[8]);
}

static u32 step1(u32 idx, int level);

/* Full HashLife result: center half after 2^(level-2) generations. Memoized. */
static u32 result(u32 idx, int level)
{
    if (nodes[idx].result != NONE) return nodes[idx].result;
    u32 res;
    if (level == BASE_LEVEL) {
        res = base_advance(idx, BASE_GENS);
    } else {
        u32 n[9], r[9], q[4], f[4];
        nine(idx, n);
        for (int i = 0; i < 9; i++) r[i] = result(n[i], level - 1);
        quarters(r, q);
        for (int i = 0; i < 4; i++) f[i] = result(q[i], level - 1);
        res = get_node(f[0], f[1], f[2], f[3]);
    }
    nodes[idx].result = res;
    return res;
}

/* Time passes only in the second phase: first phase just takes centers.
 * one_gen = 1 -> advance exactly 1 generation  (memoized in Node.step)
 * one_gen = 0 -> advance 2^(level-3) generations (half the full jump)         */
static u32 advance_centered(u32 idx, int level, int one_gen)
{
    u32 n[9], c[9], q[4], f[4];
    nine(idx, n);
    for (int i = 0; i < 9; i++) c[i] = center(n[i], level - 1);
    quarters(c, q);
    for (int i = 0; i < 4; i++)
        f[i] = one_gen ? step1(q[i], level - 1) : result(q[i], level - 1);
    return get_node(f[0], f[1], f[2], f[3]);
}

/* Center half after exactly one generation. Memoized. */
static u32 step1(u32 idx, int level)
{
    if (nodes[idx].step != NONE) return nodes[idx].step;
    u32 res = (level == BASE_LEVEL) ? base_advance(idx, 1) : advance_centered(idx, level, 1);
    nodes[idx].step = res;
    return res;
}

/* ------------------------------------------------------------------------- */
/* Universe: the root, its depth, and where it sits in world coordinates     */
/* ------------------------------------------------------------------------- */

static struct {
    u32 root;
    int level;          /* the root covers 2^level x 2^level cells            */
    i64 ox, oy;         /* world coordinate of the root's top-left cell       */
    u64 gen;
} U;

static void set_root(u32 root, int level, i64 ox, i64 oy)
{
    U.root = root; U.level = level; U.ox = ox; U.oy = oy;
}

/* Surround the root with an equal-sized empty ring on every side (level + 1). */
static void expand_root(void)
{
    int l = U.level;
    if (l >= MAX_LEVEL) fatal("The universe has outgrown the supported size (2^%d cells wide)", MAX_LEVEL);
    u32 e = empty_node(l - 1);
    u32 a = nodes[U.root].child[0], b = nodes[U.root].child[1];
    u32 c = nodes[U.root].child[2], d = nodes[U.root].child[3];
    u32 nw = get_node(e, e, e, a);
    u32 ne = get_node(e, e, b, e);
    u32 sw = get_node(e, c, e, e);
    u32 se = get_node(d, e, e, e);
    i64 s = (i64)1 << (l - 1);
    set_root(get_node(nw, ne, sw, se), l + 1, U.ox - s, U.oy - s);
}

/* True if the outer 12 of the root's 16 grandchildren are empty. */
static int outer_empty(void)
{
    u32 e = empty_node(U.level - 2);
    const Node *r = &nodes[U.root];
    const Node *a = &nodes[r->child[0]], *b = &nodes[r->child[1]];
    const Node *c = &nodes[r->child[2]], *d = &nodes[r->child[3]];
    return a->child[0] == e && a->child[1] == e && a->child[2] == e &&
           b->child[0] == e && b->child[1] == e && b->child[3] == e &&
           c->child[0] == e && c->child[2] == e && c->child[3] == e &&
           d->child[1] == e && d->child[2] == e && d->child[3] == e;
}

static void shrink_root(void)
{
    while (U.level > MIN_ROOT_LEVEL && outer_empty()) {
        i64 s = (i64)1 << (U.level - 2);
        set_root(center(U.root, U.level), U.level - 1, U.ox + s, U.oy + s);
    }
}

/* Leave the pattern inside the center quarter of the root, so it cannot
 * reach the edge of the computed region during one step / jump. */
static void pad_root(void)
{
    shrink_root();
    expand_root();
    expand_root();
}

static void sim_step(void)
{
    pad_root();
    int k = U.level;
    i64 s = (i64)1 << (k - 2);
    set_root(step1(U.root, k), k - 1, U.ox + s, U.oy + s);
    U.gen++;
}

static void sim_jump(void)
{
    pad_root();
    int k = U.level;
    i64 s = (i64)1 << (k - 2);
    u64 g = (u64)1 << (k - 3);
    set_root(advance_centered(U.root, k, 0), k - 1, U.ox + s, U.oy + s);
    U.gen = (U.gen > UINT64_MAX - g) ? UINT64_MAX : U.gen + g;
}

/* ------------------------------------------------------------------------- */
/* Loading the initial state                                                 */
/* ------------------------------------------------------------------------- */

static u32 build(const u8 *g, u32 n, i64 x, i64 y, int level)
{
    if (x >= (i64)n || y >= (i64)n) return empty_node(level);
    if (level == LEAF_LOG) {
        u32 bits = 0;
        for (int cy = 0; cy < LEAF_SIZE; cy++)
            for (int cx = 0; cx < LEAF_SIZE; cx++)
                if (x + cx < (i64)n && y + cy < (i64)n && g[(size_t)(y + cy) * n + (size_t)(x + cx)])
                    bits |= 1u << (cy * LEAF_SIZE + cx);
        return bits;
    }
    i64 h = (i64)1 << (level - 1);
    u32 nw = build(g, n, x,     y,     level - 1);
    u32 ne = build(g, n, x + h, y,     level - 1);
    u32 sw = build(g, n, x,     y + h, level - 1);
    u32 se = build(g, n, x + h, y + h, level - 1);
    return get_node(nw, ne, sw, se);
}

/* File format: "<size>;<size*size characters of 0/1>", e.g. 3;101100010 */
static u32 load_pattern(const char *path)
{
    FILE *f = fopen(path, "rb");
    if (!f) fatal("Cannot open '%s'", path);
    unsigned long long n;
    if (fscanf(f, "%llu", &n) != 1 || n == 0 || n > 32768) fatal("'%s': invalid grid size", path);
    int ch;
    do ch = fgetc(f); while (ch != EOF && isspace(ch));
    if (ch != ';') fatal("'%s': expected ';' after the grid size", path);

    size_t total = (size_t)(n * n), i = 0;
    u8 *g = (u8 *)malloc(total);
    if (!g) fatal("Out of memory reading '%s'", path);
    while (i < total && (ch = fgetc(f)) != EOF) {
        if (ch == '0' || ch == '1') g[i++] = (u8)(ch - '0');
        else if (!isspace(ch)) fatal("'%s': unexpected character '%c'", path, ch);
    }
    fclose(f);
    if (i < total) fatal("'%s': expected %zu cells, found %zu", path, total, i);

    int level = MIN_ROOT_LEVEL;
    while (((u64)1 << level) < n) level++;
    u32 root = build(g, (u32)n, 0, 0, level);
    free(g);
    set_root(root, level, 0, 0);
    U.gen = 0;
    return (u32)n;
}

/* ==== GUI ==== */

#include <SDL3/SDL.h>
#include <SDL3/SDL_main.h>

static SDL_Renderer *ren;
static struct { double cx, cy, scale; int w, h; } V;   /* camera: world point at screen center, pixels per cell */

#define RECT_BATCH 4096
static SDL_FRect rect_buf[RECT_BATCH];
static int rect_n;

static void flush_rects(void)
{
    if (rect_n) { SDL_RenderFillRects(ren, rect_buf, rect_n); rect_n = 0; }
}

static void push_rect(double x, double y, double w, double h)
{
    if (rect_n == RECT_BATCH) flush_rects();
    rect_buf[rect_n].x = (float)x; rect_buf[rect_n].y = (float)y;
    rect_buf[rect_n].w = (float)w; rect_buf[rect_n].h = (float)h;
    rect_n++;
}

/* Draw only what is visible; anything smaller than a pixel becomes one pixel. */
static void draw_node(u32 idx, int level, double x, double y)
{
    double size = ldexp(V.scale, level);
    if (x + size < 0 || y + size < 0 || x > V.w || y > V.h) return;
    if (idx == empty_node(level)) return;
    if (size <= 1.0) { push_rect(floor(x), floor(y), 1, 1); return; }

    if (level == LEAF_LOG) {
        u16 bits = canon[idx].cells;
        double cell = V.scale, gap = (cell >= 6.0) ? 1.0 : 0.0;
        for (int cy = 0; cy < LEAF_SIZE; cy++)
            for (int cx = 0; cx < LEAF_SIZE; cx++)
                if ((bits >> (cy * LEAF_SIZE + cx)) & 1)
                    push_rect(x + cx * cell, y + cy * cell, cell - gap, cell - gap);
        return;
    }
    double half = size * 0.5;
    const Node *n = &nodes[idx];
    draw_node(n->child[0], level - 1, x,        y);
    draw_node(n->child[1], level - 1, x + half, y);
    draw_node(n->child[2], level - 1, x,        y + half);
    draw_node(n->child[3], level - 1, x + half, y + half);
}

static void render(void)
{
    SDL_SetRenderDrawColor(ren, 18, 18, 22, 255);
    SDL_RenderClear(ren);
    SDL_SetRenderDrawColor(ren, 235, 235, 235, 255);
    double x = ((double)U.ox - V.cx) * V.scale + V.w * 0.5;
    double y = ((double)U.oy - V.cy) * V.scale + V.h * 0.5;
    draw_node(U.root, U.level, x, y);
    flush_rects();
    SDL_RenderPresent(ren);
}

int main(int argc, char **argv)
{
    if (argc < 2) {
        fprintf(stderr, "usage: %s <pattern file>\n  file format: <size>;<size*size cells of 0/1>, e.g. 3;101100010\n", argv[0]);
        return 1;
    }
    storage_init();
    u32 n = load_pattern(argv[1]);

    if (!SDL_Init(SDL_INIT_VIDEO)) fatal("SDL_Init failed: %s", SDL_GetError());
    SDL_Window *win = SDL_CreateWindow("Game of Life", 1280, 720, SDL_WINDOW_RESIZABLE);
    if (!win) fatal("SDL_CreateWindow failed: %s", SDL_GetError());
    ren = SDL_CreateRenderer(win, NULL);
    if (!ren) fatal("SDL_CreateRenderer failed: %s", SDL_GetError());
    SDL_SetRenderVSync(ren, 1);

    SDL_GetWindowSize(win, &V.w, &V.h);
    V.cx = n * 0.5;
    V.cy = n * 0.5;
    V.scale = fmin(32.0, 0.9 * fmin(V.w, V.h) / (double)n);

    int running = 0, jump_mode = 0, quit = 0;
    Uint64 delay_ms = 60, last = 0, shown_gen = UINT64_MAX;

    while (!quit) {
        SDL_Event ev;
        while (SDL_PollEvent(&ev)) {
            switch (ev.type) {
            case SDL_EVENT_QUIT: quit = 1; break;
            case SDL_EVENT_WINDOW_RESIZED: SDL_GetWindowSize(win, &V.w, &V.h); break;
            case SDL_EVENT_MOUSE_MOTION:
                if (ev.motion.state & (SDL_BUTTON_LMASK | SDL_BUTTON_MMASK | SDL_BUTTON_RMASK)) {
                    V.cx -= ev.motion.xrel / V.scale;
                    V.cy -= ev.motion.yrel / V.scale;
                }
                break;
            case SDL_EVENT_MOUSE_WHEEL: {
                double mx = ev.wheel.mouse_x - V.w * 0.5, my = ev.wheel.mouse_y - V.h * 0.5;
                double wx = V.cx + mx / V.scale, wy = V.cy + my / V.scale;
                double s = V.scale * pow(1.15, ev.wheel.y);
                V.scale = fmax(1e-15, fmin(256.0, s));
                V.cx = wx - mx / V.scale;
                V.cy = wy - my / V.scale;
                break;
            }
            case SDL_EVENT_KEY_DOWN:
                switch (ev.key.key) {
                case SDLK_ESCAPE: quit = 1; break;
                case SDLK_SPACE:  if (!ev.key.repeat) running = !running; break;
                case SDLK_M:      if (!ev.key.repeat) jump_mode = !jump_mode; break;
                case SDLK_N: case SDLK_RIGHT: sim_step(); break;
                case SDLK_J:      sim_jump(); break;
                case SDLK_UP:     if (delay_ms > 1) delay_ms /= 2; break;
                case SDLK_DOWN:   if (delay_ms < 2000) delay_ms *= 2; break;
                }
                break;
            }
        }

        Uint64 now = SDL_GetTicks();
        if (running && now - last >= delay_ms) {
            if (jump_mode) sim_jump(); else sim_step();
            last = now;
        }

        if (U.gen != shown_gen) {
            char title[96];
            SDL_snprintf(title, sizeof title, "Game of Life - generation %llu", (unsigned long long)U.gen);
            SDL_SetWindowTitle(win, title);
            shown_gen = U.gen;
        }
        render();
    }

    SDL_DestroyRenderer(ren);
    SDL_DestroyWindow(win);
    SDL_Quit();
    return 0;
}