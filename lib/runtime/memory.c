#include <stdlib.h>

// Contains allocation functions for different kinds of regions

// Global region
// Number of bytes per block
#define GLOBAL_BLOCK_SIZE (1024 * 128)
int helium_global_remaining = 0;
void* helium_global_next;
void* helium_global_alloc(int size) {
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
