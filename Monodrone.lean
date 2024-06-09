import Lean
import Mathlib.Order.Interval.Basic
import Mathlib.Data.List.Basic
import Mathlib.Algebra.AddTorsor
-- import Mathlib.Order.Disjoint
import Batteries.Data.RBMap
import Mathlib.Data.List.Sort
import Mathlib.Order.GaloisConnection
import Lean.Elab.Tactic.Config
import Monodrone.NoteOmega
open Lean Meta
open Batteries

/-
Step: The smallest unit of time in a sequencer. Each step can be assigned a sound.
Pattern: A sequence of steps forming a repeating musical phrase or loop.
Track: A sequence lane dedicated to a specific drum sound or instrument.
-/

/-- A pitch represented by the MIDI pitch value. -/
structure Pitch where
  pitch : UInt64
  junk : Unit := () -- workaround for https://github.com/leanprover/lean4/issues/4278
deriving Inhabited, DecidableEq, Repr

def Pitch.middleC : Pitch := { pitch := 60 }
def Pitch.raiseSemitone (p : Pitch) : Pitch := { pitch := p.pitch + 1 }
def Pitch.lowerSemitone (p : Pitch) : Pitch := { pitch := p.pitch - 1 }
def Pitch.raiseWhole (p : Pitch) : Pitch := { pitch := p.pitch + 2 }
def Pitch.lowerWhole (p : Pitch) : Pitch := { pitch := p.pitch - 2 }

def Note.lastNoteIx : Nat := 9999

/-- A Note with a location. -/
structure Note where
  pitch : Pitch
  /-- The step at which the note starts. -/
  start : Nat
  /-- The duration of the note in steps. -/
  nsteps : Nat
  /-- a Note is played for at least one step -/
  hnsteps : nsteps > 0
deriving DecidableEq, Repr

instance : Inhabited Note where
  default := { pitch := Pitch.middleC, start := 0, nsteps := 1, hnsteps := by decide }

/-- The step when the note plays last. -/
@[note_omega]
def Note.lastPlayed (n : Note) : Nat := n.start + n.nsteps - 1

def Note.overlaps (n1 n2 : Note) : Prop :=
   n2.start ≤ n1.lastPlayed && n1.start ≤ n2.lastPlayed

instance : Decidable (Note.overlaps n1 n2) := by
  simp [Note.overlaps]
  infer_instance

def Note.disjoint (n1 n2 : Note) : Prop :=
  n1.lastPlayed < n2.start || n2.lastPlayed < n1.start

instance : Decidable (Note.disjoint n1 n2) := by
  simp [Note.disjoint]
  infer_instance


theorem Note.overlaps_if_not_disjoint (n1 n2 : Note) :
    ¬ Note.disjoint n1 n2 → Note.overlaps n1 n2 := by
  simp [Note.disjoint, Note.overlaps]

theorem Note.disjoint_if_not_overlaps (n1 n2 : Note) :
    ¬ Note.overlaps n1 n2 → Note.disjoint n1 n2 := by
  simp [Note.disjoint, Note.overlaps]
  intros h₁
  omega

theorem Note.disjoint_symm (n1 n2 : Note) :
    Note.disjoint n1 n2 ↔ Note.disjoint n2 n1 := by
  simp [Note.disjoint]
  constructor <;> omega

theorem Note.overlaps_symm (n1 n2 : Note) :
    Note.overlaps n1 n2 ↔ Note.overlaps n2 n1 := by
  simp [Note.overlaps]
  constructor <;> omega

def Note.contains (n : Note) (ix : Nat) : Prop :=
  n.start ≤ ix && ix ≤ n.lastPlayed

instance : Decidable (Note.contains n ix) := by
  simp [Note.contains]
  infer_instance

def Note.containsNote (n1 n2 : Note) : Prop :=
  n1.start ≤ n2.start && n2.lastPlayed ≤ n1.lastPlayed

instance : Decidable (Note.containsNote n1 n2) := by
  simp [Note.containsNote]
  infer_instance

def Note.compare (n1 n2 : Note) : Ordering :=
  if n1.start < n2.start then Ordering.lt
  else if n1.start = n2.start then
    if n1.lastPlayed < n2.lastPlayed then Ordering.lt
    else if n2.lastPlayed < n1.lastPlayed then Ordering.gt
    else Ordering.eq
  else
    Ordering.gt

instance : LT Note where
  lt n1 n2 := Note.compare n1 n2 = Ordering.lt

instance : LE Note where
  le n1 n2 := n1 < n2 ∨ n1 = n2

/-- A track is a list of located notes, with all notes disjoint. -/
structure Track where
  notes : List Note
  /-- The notes are disjoint. -/
  hdisjoint : notes.Pairwise Note.disjoint
  junk : Unit := ()  -- workaround for https://github.com/leanprover/lean4/issues/4278
deriving Repr, DecidableEq

/--
Try to add a note to a track.
Succeeds if there is space for the note. Fails otherwise,
returning the same track. -/
def Track.addNote (t : Track) (n : Note) : Track :=
  if ht : t.notes.all (fun n' => decide (n.disjoint n')) then
  { t with
    notes := n :: t.notes
    hdisjoint := by
      simp_all only [List.all_eq_true,
        decide_eq_true_eq, not_forall, Classical.not_imp]
      simp [List.pairwise_cons, ht, t.hdisjoint]
      assumption
  }
  else t

open List in
theorem List.pairwise_map' {l : List α} {f : α → β}
    {hf : ∀ {a a' : α}, R a a' → S (f a) (f a')}
    (hl : l.Pairwise R) : (l.map f).Pairwise S := by
  induction l
  case nil => simp
  case cons a as ih =>
    simp only [map, pairwise_cons, forall_mem_map_iff, *, hl]
    constructor
    · simp only [pairwise_cons] at hl
      intros a ha
      apply hf
      apply hl.1
      assumption
    · simp only [pairwise_cons] at hl
      exact (ih hl.2)

theorem not_contains_of_disjoint_of_contains {n1 n2 : Note} {ix : Nat}
    (hdisjoint : n1.disjoint n2) (hcontains : n1.contains ix) : ¬ n2.contains ix := by
  simp [Note.disjoint, Note.contains] at *
  intros h₂
  have hn2 := n2.hnsteps
  have hn1 := n1.hnsteps
  simp_all [note_omega]
  omega

theorem disjoint_of_containsNote {nlarge nsmall m : Note}
    (hcontains : nlarge.containsNote nsmall) (hdisjoint : nlarge.disjoint m) :
    nsmall.disjoint m := by
  simp [Note.disjoint, Note.containsNote] at *
  have hnsmall := nsmall.hnsteps
  have hnlarge := nlarge.hnsteps
  simp_all [note_omega]
  omega

/-- Modify a note at the location 'loc' if it exists, as long as the
modification does not increase the the length of the note. -/
def Track.modifyNoteOfContains (t : Track) (loc : Nat) (f : Note → Note)
  (hf : ∀ (n : Note), n.containsNote (f n)) : Track :=
  { t with
    notes := t.notes.map fun note =>
      if note.contains loc then f note else note
    hdisjoint := by
      apply List.pairwise_map' (R := Note.disjoint) (S := Note.disjoint) t.hdisjoint
      intros a a'
      intros haa'
      split_ifs
      case pos ha ha' =>
        have hcontra := not_contains_of_disjoint_of_contains haa' ha
        contradiction
      case neg ha ha' =>
        apply disjoint_of_containsNote
        apply hf
        apply haa'
      case pos ha ha' =>
        rw [Note.disjoint_symm]
        apply disjoint_of_containsNote
        apply hf
        rw [Note.disjoint_symm]
        apply haa'
      case neg ha ha' =>
        exact haa'
  }

/--
Try to remove note at location 'loc'.
-/
def Track.removeNoteAt (t : Track) (loc : Nat) : Track :=
  { t with
    notes := t.notes.filter (fun note => note.contains loc),
    hdisjoint := List.Pairwise.filter _ t.hdisjoint
  }

def Track.empty : Track := { notes := [], hdisjoint := by simp [] }

def Track.default : Track where
  notes := [ { pitch := Pitch.middleC, start := 0, nsteps := 1, hnsteps := by decide } ]
  hdisjoint := by simp [Note.disjoint]

instance : Inhabited Track where
  default := Track.empty

def Track.maxLength : Nat := 9999

structure Cursor where
  /-- How far the selection extends. -/
  a : Fin Track.maxLength
   /-- Where the cursor is located. -/
  b : Fin Track.maxLength
deriving DecidableEq, Repr, DecidableEq

def Cursor.atbegin : Cursor :=
  { a := ⟨0, by simp [Track.maxLength]⟩,
    b := ⟨0, by simp [Track.maxLength]⟩
  }

instance : Inhabited Cursor where
  default := .atbegin

inductive CursorMoveAction
| up (d : Nat)
| down (d : Nat)

def CursorMoveAction.act (c : Cursor)
    (act : CursorMoveAction) : Cursor :=
  match act with
  | .up d => { c with b := ⟨c.b.val - d, by omega⟩ }
  | .down d => { c with b :=
    ⟨Nat.min (c.b.val + d) (Track.maxLength - 1),
      Nat.lt_of_le_of_lt (Nat.min_le_right ..) (by simp [Track.maxLength])⟩
  }

/-- Todo: show that moveDown / moveUp are a galois connection. -/

def Cursor.moveDownOne (c : Cursor) : Cursor := (CursorMoveAction.down 1).act c
def Cursor.moveUpOne (c : Cursor) : Cursor := (CursorMoveAction.up 1).act c

def Cursor.moveDownHalfPage (c : Cursor) : Cursor := (CursorMoveAction.down 10).act c
def Cursor.moveUpHalfPage (c : Cursor) : Cursor := (CursorMoveAction.up 10).act c

class Patchable (α : Type) (δ : Type) extends VAdd δ α where
  /-- Given the diff `f -δ→ g` and `f`, compute `g -(f @⁻¹ δ)→ f`.
  Note that the diff can be inverted sensibly only at the element it was
  applied to. -/
  reverse : α → δ → δ


@[inherit_doc] infixr:73 " @⁻¹ " => Patchable.reverse

/-- apply the patch  `a -d→ ` to get `(apply2 a d).snd`,
and simultaneously make the patch `(apply2 a d).snd -(apply2 a d).snd→ a`. -/
def Patchable.apply2 [Patchable α δ] (a : α) (d : δ) : α × δ :=
  (d +ᵥ a, Patchable.reverse a d)

@[simp]
theorem Patchable.fst_apply2 [Patchable α δ] (a : α) (d : δ) : (Patchable.apply2 a d).fst = d +ᵥ a := by
  simp [Patchable.apply2]

@[simp]
theorem Patchable.snd_apply2 [Patchable α δ] (a : α) (d : δ) : (Patchable.apply2 a d).snd = Patchable.reverse a d := by
  simp [Patchable.apply2]

class Diffable (α : Type) (δ : outParam Type) extends Patchable α δ, VSub δ α

class LawfulPatchable (α : Type) (δ : outParam Type) [Patchable α δ] where
  reverse_vadd_vadd {a : α} {d : δ} : (a @⁻¹ d) +ᵥ (d +ᵥ a) = a
  vadd_reverse_reverse {a : α} {d : δ} : (d +ᵥ a) @⁻¹ a @⁻¹ d = d

/-- TODO: how to extend LawfulPatchable? -/
class LawfulDiffable (α : Type) (δ : outParam Type) [Diffable α δ]
    extends LawfulPatchable α δ where
  vsub_vadd {a b : α} : (b -ᵥ a) +ᵥ a = b
  reverse_vsub {a b : α} : b @⁻¹ (a -ᵥ b) = b -ᵥ a

attribute [simp] LawfulPatchable.reverse_vadd_vadd
attribute [simp] LawfulPatchable.vadd_reverse_reverse
attribute [simp] LawfulDiffable.vsub_vadd
attribute [simp] LawfulDiffable.reverse_vsub

structure NaiveDiff (α : Type) where
  new : α

instance  : Diffable α (NaiveDiff α) where
  vadd d _ := d.new
  vsub new _cur := { new := new }
  reverse cur _cur2new := { new := cur }

instance : LawfulDiffable α (NaiveDiff α) where
  vsub_vadd := by simp [(· -ᵥ ·), (· +ᵥ ·), VAdd.vadd, Patchable.reverse]
  reverse_vadd_vadd := by simp [(· -ᵥ ·), (· +ᵥ ·), VAdd.vadd, Patchable.reverse]
  vadd_reverse_reverse := by simp [(· -ᵥ ·), (· +ᵥ ·), VAdd.vadd, Patchable.reverse]
  reverse_vsub := by simp [(· -ᵥ ·), (· +ᵥ ·), VAdd.vadd, Patchable.reverse]

/--
A data structure which maintains the history of a given type.
past₂ ←p-  past₁ ←p- cur  -n→ c₁ -n→ c₂ ... -/
structure HistoryStack (α : Type) (δ : Type) where
  /- upon being applied to `cur`, gives previous element. -/
  historyPrev : List δ
  cur : α
   /- upon being applied, gives next element. -/
  historyNext: List δ
deriving Inhabited, Repr


def HistoryStack.init {α : Type} (a : α) : HistoryStack α δ where
  historyPrev := []
  cur := a
  historyNext := []

def HistoryStack.prev (h : HistoryStack α δ) [Patchable α δ] : HistoryStack α δ :=
  match h.historyPrev with
  | [] => h
  | p :: ps =>
    let (next, patch) := Patchable.apply2 h.cur p
    { h with
      cur := next,
      historyPrev := ps,
      historyNext := patch :: h.historyNext
    }

def HistoryStack.next (h : HistoryStack α δ) [Patchable α δ] : HistoryStack α δ :=
  match h.historyNext with
  | [] => h
  | a :: as =>
    let (next, patch) := Patchable.apply2 h.cur a
    {
      cur := next,
      historyPrev := patch :: h.historyPrev,
      historyNext := as
    }

/-- Todo: show that prev / next are a galois connection. -/
theorem HistoryStack.prev_next_eq_self_of_next_ne [Patchable α δ] [LawfulPatchable α δ]
    (h : HistoryStack α δ) (hprev : h.historyNext ≠ []) :
    (HistoryStack.prev (HistoryStack.next h)) = h := by
  rcases h with ⟨prev, cur, next⟩
  simp [HistoryStack.prev, HistoryStack.next]
  cases next <;> cases prev <;> simp_all

theorem HistoryStack.next_prev_eq_self_of_prev_ne [Patchable α δ] [LawfulPatchable α δ]
    (h : HistoryStack α δ)
    (hprev : h.historyPrev ≠ []) :
    (HistoryStack.next (HistoryStack.prev h)) = h := by
  rcases h with ⟨prev, cur, next⟩
  simp [HistoryStack.prev, HistoryStack.next]
  cases next <;> cases prev <;> simp_all

/-- Wipe away history next, making the actions as 'cur', and keeping history prev. -/
def HistoryStack.setForgettingFuture [DecidableEq α] [Diffable α δ]
    (newcur : α) (h : HistoryStack α δ) : HistoryStack α δ where
  cur := newcur
  historyPrev :=
    if h.cur = newcur then h.historyPrev
    else (h.cur -ᵥ newcur) :: h.historyPrev
  historyNext := []

/-- If we actually pushed a new state, then undo will take us back to the old state. -/
theorem HistoryStack.cur_prev_setForgettingFuture_eq_cur [DecidableEq α]
    [Diffable α δ] [LawfulDiffable α δ]
    (h : HistoryStack α δ) (newcur : α) (hnewcur : h.cur ≠ newcur):
    (HistoryStack.setForgettingFuture newcur h).prev.cur = h.cur := by
  simp [HistoryStack.setForgettingFuture, prev, hnewcur]

/--  Undo followed by a redo will keep us at the current state. -/
theorem HistoryStack.cur_next_prev_setForgettingFuture_eq_cur [DecidableEq α]
    [Diffable α δ] [LawfulPatchable α δ]
    (h : HistoryStack α δ) (newcur : α) (hnewcur : h.cur ≠ newcur) :
    (HistoryStack.setForgettingFuture newcur h).prev.next.cur = newcur := by
  simp [HistoryStack.setForgettingFuture, prev, next, hnewcur]

/-- Wipe away history next, making the actions as `cur`, and keeping history prev. -/
def HistoryStack.modifyForgettingFuture [DecidableEq α] [Diffable α δ]
    (f : α → α) (h : HistoryStack α δ) : HistoryStack α δ :=
  HistoryStack.setForgettingFuture (f h.cur) h

/-- Wipe away history next, applying patch `p`, and keeping history prev. -/
def HistoryStack.patchForgettingFuture [DecidableEq α] [Diffable α δ]
    (h : HistoryStack α δ) (p : δ) : HistoryStack α δ where
  cur := p +ᵥ h.cur
  historyPrev := (h.cur @⁻¹ p) :: h.historyPrev
  historyNext := []

/--  Undo will take us back to the previous state. -/
theorem HistoryStack.cur_prev_patchForgettingFuture_eq [DecidableEq α]
    [Diffable α δ] [LawfulDiffable α δ]
    (h : HistoryStack α δ) (patch : δ)  :
    (HistoryStack.patchForgettingFuture h patch).prev.cur = h.cur := by
  simp [HistoryStack.patchForgettingFuture, prev, next]


structure RawContext where
  lastPlacedPitch : Pitch
  track : HistoryStack Track (NaiveDiff Track)
  cursor : HistoryStack Cursor (NaiveDiff Cursor)
  junk : Unit := () -- Workaround for: 'https://github.com/leanprover/lean4/issues/4278'
deriving Inhabited

def RawContext.empty : RawContext := {
    track := HistoryStack.init Track.empty,
    cursor := HistoryStack.init .atbegin,
    lastPlacedPitch := Pitch.middleC
}

def RawContext.default : RawContext := {
    track := HistoryStack.init Track.default,
    cursor := HistoryStack.init .atbegin,
    lastPlacedPitch := Pitch.middleC
}

namespace ffi
/-!

#### C FFI

₂

We follow [json-c](https://json-c.github.io/json-c/json-c-0.17/doc/html/json__object_8h.html) naming conventions:

- `monodrone_` prefix
- `object_<type>_length` to count the number of elements in an object of type <type>
- `object_get_<type>` to get an element of type <type>
-/

@[export monodrone_new_context]
def newContext (_ : Unit) : RawContext := RawContext.default

@[export monodrone_track_length]
def trackLength (ctx : @&RawContext) : UInt64 := ctx.track.cur.notes.length.toUInt64

@[export monodrone_track_get_note]
def trackGetNote (ctx : @&RawContext) (ix : UInt64) : Note :=
  ctx.track.cur.notes.get! ix.toNat

@[export monodrone_note_get_pitch]
def noteGetPitch (n : Note) : UInt64 := n.pitch.pitch

@[export monodrone_note_get_start]
def noteGetStart (n : Note) : UInt64 := n.start.toUInt64

@[export monodrone_note_get_nsteps]
def noteGetNsteps (n : Note) : UInt64 := n.nsteps.toUInt64

@[export monodrone_ctx_cursor_a]
def cursorGetA (ctx : @&RawContext): UInt64 :=
  ctx.cursor.cur.a.val.toUInt64

@[export monodrone_ctx_cursor_b]
def cursorGetB (ctx : @&RawContext): UInt64 :=
  ctx.cursor.cur.b.val.toUInt64

def RawContext.moveDownOne (ctx : RawContext) : RawContext :=
  { ctx with cursor := ctx.cursor.modifyForgettingFuture Cursor.moveDownOne }

def RawContext.moveUpOne (ctx : RawContext) : RawContext :=
  { ctx with cursor := ctx.cursor.modifyForgettingFuture Cursor.moveUpOne }

def RawContext.moveDownHalfPage (ctx : RawContext) : RawContext :=
  { ctx with cursor := ctx.cursor.modifyForgettingFuture Cursor.moveDownHalfPage }

def RawContext.moveUpHalfPage (ctx : RawContext) : RawContext :=
  { ctx with cursor := ctx.cursor.modifyForgettingFuture Cursor.moveUpHalfPage }

def RawContext.removeNote (ctx : RawContext) : RawContext :=
  let newTrack := ctx.track.modifyForgettingFuture fun t =>
    t.removeNoteAt ctx.cursor.cur.b.val
  { ctx with track := newTrack }

def RawContext.addNote (ctx : RawContext) : RawContext :=
  let pitch := ctx.lastPlacedPitch
  let start := ctx.cursor.cur.b.val
  let nsteps := 1
  let newNote : Note := {
      pitch := pitch,
      start := start,
      nsteps := nsteps, hnsteps := by decide
    }
  let newTrack := ctx.track.modifyForgettingFuture fun t =>
    t.removeNoteAt start |>.addNote newNote
  { ctx with track := newTrack }

def RawContext.moveNoteUpSemitone (ctx : RawContext) : RawContext := sorry

def RawContext.moveNoteDownSemitone (ctx : RawContext) : RawContext := sorry

def RawContext.undoAction (ctx : RawContext) : RawContext :=
  { ctx with track := ctx.track.prev }

def RawContext.redoAction (ctx : RawContext) : RawContext :=
  { ctx with track := ctx.track.next }

def RawContext.undoMovement (ctx : RawContext) : RawContext :=
  { ctx with cursor := ctx.cursor.prev }

def RawContext.redoMovement (ctx : RawContext) : RawContext :=
  { ctx with cursor := ctx.cursor.next }

end ffi
