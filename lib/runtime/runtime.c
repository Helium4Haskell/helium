#include <stdlib.h>
#include <stdio.h>
#include <pthread.h>
#include <threads.h>
#include <limits.h>

// The real main: runs the user defined main using unsafePerformIO
extern int real_main(void);

// Contains allocation functions for different kinds of regions

// Global region
// Number of bytes per block
#define GLOBAL_BLOCK_SIZE (1024 * 128)
int helium_global_remaining = 0;
void* helium_global_next;

int total_memory = 0;

void* helium_global_common_alloc(int size) {
  if (size > helium_global_remaining) {
    // Allocate new block
    helium_global_next = malloc(GLOBAL_BLOCK_SIZE);
    helium_global_remaining = GLOBAL_BLOCK_SIZE;
  }

  helium_global_remaining -= size;
  void* pointer = helium_global_next;
  helium_global_next += size;

  return pointer;
}

void* helium_global_fn_alloc(int size) {
  void* pointer = helium_global_common_alloc(size);
#if defined(DEBUG)
  total_memory += size;
#endif

  return pointer;
}

void* helium_global_ds_alloc(int size) {
  return helium_global_common_alloc(size);
}

void print_memory_usage() {
  printf("memory alloc: %d\n", total_memory);
}

void* thread_main(void* arg) {
  return (void*)real_main();
}

// entry point of the runtime: runs the use program in a seperate thread
int main() {
  int err;
  pthread_t tid;
  pthread_attr_t tattr;
  void *tret;

  // default stack size is not enough
  size_t size = PTHREAD_STACK_MIN + 0x80000;

  err = pthread_attr_init(&tattr);
  err = pthread_attr_setstacksize(&tattr, size);
  err = pthread_create(&tid, &tattr, thread_main, NULL);

  if (err != 0) {
    printf("can′t create thread\n");
    exit(1);
  }

  err = pthread_join(tid, &tret);
  if (err != 0) {
    printf("can′t join with thread\n");
    exit(1);
  }

#ifdef defined(DEBUG)
  print_memory_usage();
#endif

  return (int)tret;
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
