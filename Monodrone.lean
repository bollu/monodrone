import Lean
import Mathlib.Order.Interval.Basic
import Mathlib.Data.List.Basic
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

structure Multicursor  where
  cursor : Fin Track.maxLength -- main cursor position.
  cursors : List (Fin Track.maxLength) -- stack of cursors. Main cursor is the first one in the list.
  junk : Unit := () -- workaround for
deriving DecidableEq, Repr

def Multicursor.atbegin : Multicursor := { cursor :=  ⟨0, by simp[Track.maxLength]⟩, cursors := [] }

instance : Inhabited Multicursor where
  default := .atbegin

structure RawContext where
  track : Track
  cursors : Multicursor
  junk : Unit := ()-- workaround for https://github.com/leanprover/lean4/issues/4278
deriving Inhabited, DecidableEq, Repr

def RawContext.empty : RawContext := {
    track := Track.empty,
    cursors := Multicursor.atbegin
}

def RawContext.default : RawContext := {
    track := Track.default,
    cursors := Multicursor.atbegin
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

end ffi
