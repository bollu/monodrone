#include <stdio.h>
#include <stdint.h>

void lean_initialize_runtime_module ();
void lean_io_mark_end_initialization ();
void initialize_Monodrone(uint8_t builtin, void *world);


void *lean_box(uint64_t n) {
  return (void *)(((size_t)(n) << 1) | 1);
}

void *monodrone_new_context(void *x);
void lean_inc_ref_cold(void *x);
uint64_t monodrone_track_length(void *x);

int main() {
  lean_initialize_runtime_module();
  initialize_Monodrone(1, lean_box(0));
  lean_io_mark_end_initialization();
  
  void *ctx = monodrone_new_context(lean_box(0));
  printf("ctx: %x\n", ctx);
  // lean_inc_ref_cold(ctx);
  for(int i = 0; i < 10; ++i) {
    int len = monodrone_track_length(ctx);
    printf("length: %d\n", len);
  }
  return 0;
}

