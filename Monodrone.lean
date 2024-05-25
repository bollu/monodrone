import Lean
import Mathlib.Order.Interval.Basic
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
  pitch : UInt32
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

/-- A track is a list of located notes, with all notes disjoint. -/
structure Track where
  notes : List Note
  /-- The notes are disjoint. -/
  hdisjoint : notes.Pairwise Note.disjoint
  /-- The notes are sorted -/
  hsorted : notes.Sorted (· < ·)

deriving DecidableEq, Repr

def Track.empty : Track := { notes := [], hdisjoint := by simp, hsorted := by simp }

instance : Inhabited Track where
  default := Track.empty

structure RawContext where
  tracks : Track

structure LawfulRawContext extends RawContext where

def RawContext.empty : RawContext := {
    tracks := Track.empty
}

def LawfulRawContext.empty : LawfulRawContext := {
    tracks := Track.empty
}

namespace ffi
/-!

#### C FFI

We follow [json-c](https://json-c.github.io/json-c/json-c-0.17/doc/html/json__object_8h.html) naming conventions:

- `monodrone_` prefix
- `object_<type>_length` to count the number of elements in an object of type <type>
- `object_get_<type>` to get an element of type <type>
-/

@[export monodrone_new_context]
def newContext (_ : Unit) : LawfulRawContext := LawfulRawContext.empty

@[export monodrone_track_length]
def trackLength (ctx : @&RawContext) : Nat := ctx.tracks.notes.length

@[export monodrone_track_get_note]
def trackGetNote (ctx : @&RawContext) (ix : UInt32) : Note :=
  ctx.tracks.notes.get! ix.toNat

@[export monodrone_note_get_pitch]
def noteGetPitch (n : @&Note) : UInt32 := n.pitch.pitch

@[export monodrone_note_get_start]
def noteGetStart (n : @&Note) : UInt32 := n.start.toUInt32

@[export monodrone_note_get_nsteps]
def noteGetNsteps (n : @&Note) : UInt32 := n.nsteps.toUInt32

end ffi
