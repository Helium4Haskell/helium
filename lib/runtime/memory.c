#include <stdlib.h>
#include <stdio.h>

// Contains allocation functions for different kinds of regions

// Global region
// Number of bytes per block
#define GLOBAL_BLOCK_SIZE (1024 * 128)
int helium_global_remaining = 0;
void* helium_global_next;

#if defined(DEBUG)
int total_memory = 0;
#endif

void* helium_global_alloc(int size) {
  if (size > helium_global_remaining) {
    // Allocate new block
    helium_global_next = malloc(GLOBAL_BLOCK_SIZE);
    helium_global_remaining = GLOBAL_BLOCK_SIZE;
  }
  helium_global_remaining -= size;
  void* pointer = helium_global_next;
  helium_global_next += size;

#if defined(DEBUG)
  total_memory += size;
#endif

  return pointer;
}

// Utilities to debug thunk evaluation
// To enable, uncomment calls to trace_thunk_eval and trace_thunk_done in IridiumLangEval.iridium
struct Thunk {
  long header;
  struct Thunk* next;
  char* fn;
  short remaining;
  short given;
  // ...arguments
};

void trace_thunk_idx(struct Thunk* thunk, int idx) {
  printf("Thunk, address = %ld, remaining = %d, given = %d, index in chain = %d\n", (long) thunk, thunk->remaining, thunk->given, idx);
  if (thunk->remaining == 32766) {
    printf("Evaluated\n\n");
    return;
  }

  printf("Function = ");
  char* charPtr = &thunk->fn[-1];
  while (*charPtr != 0) {
    putchar(*charPtr);
    charPtr = &charPtr[-1];
  }
  printf("\n");

  if (thunk->remaining == 32767) {
    printf("Blackhole\n\n");
    return;
  }

  if (thunk->remaining > 0) {
    printf("Unsaturated");
  } else if (thunk->remaining == 0) {
    printf("Saturated");
  } else if (thunk->given > -thunk->remaining) {
    printf("Oversaturated self");
  } else {
    printf("Oversaturated target");
  }

  if (thunk->next != thunk) {
    printf(", next: ");
    trace_thunk_idx(thunk->next, idx + 1);
  } else {
    printf("\n\n");
  }
}

void trace_thunk_eval(struct Thunk* thunk) {
  printf("Evaluating thunk: ");
  trace_thunk_idx(thunk, 0);
}

void trace_thunk_done(struct Thunk* thunk) {
  printf("Evaluated thunk %ld, value = %ld\n", (long) thunk, (long) thunk->fn);
}
