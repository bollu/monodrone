import Lean
import Mathlib.Order.Interval.Basic
import Mathlib.Data.List.Basic
import Mathlib.Algebra.AddTorsor
-- import Mathlib.Order.Disjoint
import Batteries.Data.RBMap
import Mathlib.Data.List.Sort
open Lean
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
def Note.end (n : Note) : Nat := n.start + n.nsteps - 1

def Note.overlaps (n1 n2 : Note) : Prop := n1.start < n2.end && n2.start < n1.end

def Note.disjoint (n1 n2 : Note) : Prop := n1.end < n2.start || n2.end < n1.start

def Note.compare (n1 n2 : Note) : Ordering :=
  if n1.start < n2.start then Ordering.lt
  else if n1.start = n2.start then
    if n1.end < n2.end then Ordering.lt
    else if n2.end < n1.end then Ordering.gt
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
  /-- The notes are sorted -/
  hsorted : notes.Sorted (· ≤ ·)
  junk : Unit := ()  -- workaround for https://github.com/leanprover/lean4/issues/4278
deriving DecidableEq, Repr

def Track.empty : Track := { notes := [], hdisjoint := by simp [], hsorted := by simp [] }

def Track.default : Track where
  notes := [ { pitch := Pitch.middleC, start := 0, nsteps := 1, hnsteps := by decide } ]
  hdisjoint := by simp [Note.disjoint]
  hsorted := by simp [Note.compare]

instance : Inhabited Track where
  default := Track.empty


def Track.maxLength : Nat := 9999

structure Cursor where
  a : Fin Track.maxLength
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

inductive NoteAction
| toggleNote
| moveNoteUpSemitone
| moveNoteDownSemitone
deriving Inhabited, DecidableEq, Repr

class Diffable (α : Type) (δ : outParam Type) extends VAdd δ α, VSub δ α where
  /-- Given the diff `f -δ→ g` and `f`, compute `g -(f @⁻¹ δ)→ f`.
  Note that the diff can be inverted sensibly only at the element it was
  applied to. -/
  reverse : α → δ → δ


@[inherit_doc] infixr:73 " @⁻¹ " => Diffable.reverse

/-- apply the patch  `a -d→ ` to get `(apply2 a d).snd`,
and simultaneously make the patch `(apply2 a d).snd -(apply2 a d).snd→ a`. -/
def Diffable.apply2 [Diffable α δ] (a : α) (d : δ) : α × δ :=
  (d +ᵥ a, Diffable.reverse a d)

@[simp]
theorem Diffable.fst_apply2 [Diffable α δ] (a : α) (d : δ) : (Diffable.apply2 a d).fst = d +ᵥ a := by
  simp [Diffable.apply2]

@[simp]
theorem Diffable.snd_apply2 [Diffable α δ] (a : α) (d : δ) : (Diffable.apply2 a d).snd = Diffable.reverse a d := by
  simp [Diffable.apply2]

class LawfulDiffable (α : Type) (δ : outParam Type) extends Diffable α δ where
  vsub_vadd {a b : α} : (b -ᵥ a) +ᵥ a = b
  reverse_vadd_vadd {a : α} {d : δ} : (a @⁻¹ d) +ᵥ (d +ᵥ a) = a
  vadd_reverse_reverse {a : α} {d : δ} : (d +ᵥ a) @⁻¹ a @⁻¹ d = d
  reverse_vsub {a b : α} : b @⁻¹ (a -ᵥ b) = b -ᵥ a

attribute [simp] LawfulDiffable.reverse_vadd_vadd
attribute [simp] LawfulDiffable.vadd_reverse_reverse
attribute [simp] LawfulDiffable.vsub_vadd
attribute [simp] LawfulDiffable.reverse_vsub

structure NaiveDiff (α : Type) where
  new : α

instance diffableNaiveDiff : Diffable α (NaiveDiff α) where
  vadd d _ := d.new
  vsub new _cur := { new := new }
  reverse cur _cur2new := { new := cur }

instance : LawfulDiffable α (NaiveDiff α) where
  vsub_vadd := by simp [(· -ᵥ ·), (· +ᵥ ·), VAdd.vadd, Diffable.reverse]
  reverse_vadd_vadd := by simp [(· -ᵥ ·), (· +ᵥ ·), VAdd.vadd, Diffable.reverse]
  vadd_reverse_reverse := by simp [(· -ᵥ ·), (· +ᵥ ·), VAdd.vadd, Diffable.reverse]
  reverse_vsub := by simp [(· -ᵥ ·), (· +ᵥ ·), VAdd.vadd, Diffable.reverse]

/-- A data structure which maintains the history of a given type. -/
structure HistoryStack (α : Type) [Diffable α δ] where
  historyPrev : List δ  -- upon being applied, gives previous element.
  cur : α
  historyNext: List δ -- upon being applied, gives next element
deriving Inhabited, Repr

instance [DecidableEq α] : DecidableEq (HistoryStack α) := fun a b => by
  -- rintros ⟨prev, cur, next⟩ := a
  sorry

/--  past₂ ←p  past₁ ←p cur  -n→ c₁ -n→ c₂ ... -/
def HistoryStack.init {α : Type} [Diffable α δ] (a : α) : HistoryStack α where
  historyPrev := []
  cur := a
  historyNext := []

/--
Given a state as follows:
 past₂ ←p-  past₁ ←p- cur  -n→ c₁ -n→ c₂ ... -/
--/
def HistoryStack.prev [Diffable α δ] (h : HistoryStack α) : HistoryStack α :=
  match h.historyPrev with
  | [] => h
  | p :: ps =>
    let (next, patch) := Diffable.apply2 h.cur p
    { h with
      cur := next,
      historyPrev := ps,
      historyNext := patch :: h.historyNext
    }

def HistoryStack.next [Diffable α δ] (h : HistoryStack α) : HistoryStack α :=
  match h.historyNext with
  | [] => h
  | a :: as =>
    let (next, patch) := Diffable.apply2 h.cur a
    {
      cur := next,
      historyPrev := patch :: h.historyPrev,
      historyNext := as
    }


/-- Todo: show that prev / next are a galois connection. -/

theorem HistoryStack.prev_next_eq_self_of_next_ne
    (h : HistoryStack α) (hprev : h.historyNext ≠ []) :
    (HistoryStack.prev (HistoryStack.next h)) = h := by
  rcases h with ⟨prev, cur, next⟩
  simp [HistoryStack.prev, HistoryStack.next]
  cases next <;> cases prev <;> simp_all

theorem HistoryStack.next_prev_eq_self_of_prev_ne
    (h : HistoryStack α)
    (hprev : h.historyPrev ≠ []) :
    (HistoryStack.next (HistoryStack.prev h)) = h := by
  rcases h with ⟨prev, cur, next⟩
  simp [HistoryStack.prev, HistoryStack.next]
  cases next <;> cases prev <;> simp_all

/-- Wipe away history next, making the actions as 'cur', and keeping history prev. -/
def HistoryStack.setForgettingFuture [DecidableEq α]
    (newcur : α) (h : HistoryStack α) : HistoryStack α where
  cur := newcur
  historyPrev :=
    if h.cur = newcur then h.historyPrev
    else (h.cur -ᵥ newcur) :: h.historyPrev
  historyNext := []

/-- If we actually pushed a new state, then undo will take us back to the old state. -/
theorem HistoryStack.cur_prev_setForgettingFuture_eq_cur [DecidableEq α]
    (h : HistoryStack α) (newcur : α) (hnewcur : h.cur ≠ newcur):
    (HistoryStack.setForgettingFuture newcur h).prev.cur = h.cur := by
  simp [HistoryStack.setForgettingFuture, prev, hnewcur]

/--  undo followed by a redo will keep us at the current state. -/
theorem HistoryStack.cur_next_prev_setForgettingFuture_eq_cur [DecidableEq α]
    (h : HistoryStack α) (newcur : α) (hnewcur : h.cur ≠ newcur):
    (HistoryStack.setForgettingFuture newcur h).prev.next.cur = newcur := by
  simp [HistoryStack.setForgettingFuture, prev, next, hnewcur]

/-- Wipe away history next, making the actions as 'cur', and keeping history prev. -/
def HistoryStack.modifyForgettingFuture [DecidableEq α]
    (f : α → α) (h : HistoryStack α) : HistoryStack α :=
  HistoryStack.setForgettingFuture (f h.cur) h


structure RawContext where
  track : Track
  cursor : HistoryStack Cursor
  junk : Unit := () -- Workaround for: 'https://github.com/leanprover/lean4/issues/4278'
deriving Inhabited, DecidableEq

def RawContext.empty : RawContext := {
    track := Track.empty,
    cursor := HistoryStack.init .atbegin,
}

def RawContext.default : RawContext := {
    track := Track.default,
    cursor := HistoryStack.init .atbegin,
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
def trackLength (ctx : @&RawContext) : UInt64 := ctx.track.notes.length.toUInt64

@[export monodrone_track_get_note]
def trackGetNote (ctx : @&RawContext) (ix : UInt64) : Note :=
  ctx.track.notes.get! ix.toNat

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

def RawContext.toggleNote (ctx : RawContext) : RawContext := sorry
def RawContext.moveNoteUpSemitone (ctx : RawContext) : RawContext := sorry
def RawContext.moveNoteDownSemitone (ctx : RawContext) : RawContext := sorry

def RawContext.undo (ctx : RawContext) : RawContext := sorry
def RawContext.redo (ctx : RawContext) : RawContext := sorry

end ffi
