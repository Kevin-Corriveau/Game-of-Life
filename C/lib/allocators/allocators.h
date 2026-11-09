#pragma once

/* 
    This file is a collection of allocator alternatives to malloc.
    They should be used when more context about the allocation strategy is available.
    They were designed for Windows only.
*/


typedef void *(*Allocator)(size_t size);

#ifdef ALLOCATORS_INCLUDE
#undef ALLOCATORS_INCLUDE

#include "linear.h"

#endif
