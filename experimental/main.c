#include <stdio.h>
#include <stdint.h>
#include <lean/lean.h>

void lean_initialize_runtime_module ();
void lean_io_mark_end_initialization ();
void initialize_Monodrone(uint8_t builtin, void *world);
void *monodrone_ctx_move_down_one(void *ctx);
void *monodrone_ctx_move_up_one(void *ctx);
uint64_t monodrone_ctx_cursor_b(void *ctx);
uint64_t monodrone_note_get_pitch (void *note);
void *monodrone_track_get_note(void *track, int ix);
uint64_t monodrone_note_get_start (void *note);
uint64_t monodrone_note_get_nsteps (void *note);

void *monodrone_ctx_lower_semitone(void *ctx);
void *monodrone_ctx_raise_semitone(void *ctx);

void *monodrone_new_context(void *x);
uint64_t monodrone_track_length(void *x);

void print_track(void *ctx) {
  lean_inc_ref(ctx);
  int len = monodrone_track_length(ctx);
  printf("track length: %d\n", len);

   for(int i = 0; i < len; ++i) {
     lean_inc_ref(ctx);
     printf("getting note [%d]...", i); fflush(stdout);
     void *note = monodrone_track_get_note(ctx, i);
     lean_inc_ref(note);
     uint64_t pitch = monodrone_note_get_pitch(note);
     lean_inc_ref(note);
     uint64_t start = monodrone_note_get_start(note);
     lean_inc_ref(note);
     uint64_t nsteps = monodrone_note_get_nsteps(note);
     printf("note [%d]: pitch=%llu, start=%llu, nsteps=%llu\n", i, pitch, start, nsteps);
   }
}
int main() {
  lean_initialize_runtime_module();
  initialize_Monodrone(1, lean_box(0));
  lean_io_mark_end_initialization();
  
  void *ctx = monodrone_new_context(lean_box(0));
  printf("ctx: %p\n", ctx);

  for (int i = 0; i < 5; ++i) { print_track(ctx); }

  for(int i = 0; i < 1; ++i) {
    lean_inc_ref(ctx);
    int len = monodrone_track_length(ctx);
    printf("length: %d\n", len);
  }

  for (int i = 0; i < 5; ++i) { print_track(ctx); }

  for(int i = 0; i < 1; ++i) {
    lean_inc_ref(ctx); int cursor_loc = monodrone_ctx_cursor_b(ctx);

    printf("moving up one [loc=%5d]...", cursor_loc);
    lean_inc_ref(ctx);
    ctx = monodrone_ctx_move_up_one(ctx);
    printf("; moved!\n");

  }

  for (int i = 0; i < 5; ++i) { print_track(ctx); }
  return 0;

  // lean_inc_ref(ctx);
  // printf("track length: %d\n", monodrone_track_length(ctx));

  // printf("lowering semitone..."); fflush(stdout);
  // lean_inc_ref(ctx);
  // ctx = monodrone_ctx_lower_semitone(ctx);
  // printf("; lowered!\n");

  // print_track(ctx);
  // print_track(ctx);

  // printf("raising semitone...");
  // lean_inc_ref(ctx);
  // ctx = monodrone_ctx_raise_semitone(ctx);
  // printf("; raised!\n");

  // print_track(ctx);

  // return 0;
}

