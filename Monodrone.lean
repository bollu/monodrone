import Lean
import Mathlib.Order.Interval.Basic
-- import Mathlib.Order.Disjoint
import Batteries.Data.RBMap
open Lean

def foo : Interval Nat := ⊥

/-! A pitch is represented by the MIDI sequence. -/
abbrev Pitch : Type := Nat

/-! A note is a pitch and a duration.
  Note that these intervals maybe empty -/
structure I where
  start : Nat
  length : Nat

def I.compare (i j : I) : Ordering :=
  if i.start < j.start then Ordering.lt
  else if i.start > j.start then Ordering.gt
  else if i.length < j.length then Ordering.lt
  else if i.length > j.length then Ordering.gt
  else Ordering.eq

def I.isDisjoint (i j : I) : Prop :=
  i.start + i.length < j.start -- I ends before J starts
  || j.start + j.length < i.start -- J ends before I starts

-- TODO: this will not work, each I needs its own sequence number. Cannot directly reuse mathlib.
/-! A sequence for a pitcj, which consists of intervals when notes are being played. -/
structure PitchSequence where
  intervals : List I
deriving Inhabited

/-- Invariants for a `PitchSequence` that ought to hold. -/
structure IsGoodTrack (r : PitchSequence) : Prop where
  /-- at least one interval must not be bottom -/
  nontrvial : ∃ (i : I), i ∈ r.intervals ∧ i.length > 0
  /-- all intervals in a track must be pairwise disjoint. -/
  intervalsDisjoint : ∀ (i j : I), i ∈ r.intervals → j ∈ r.intervals → i ≠ j →
     i.isDisjoint j

abbrev Track := { r : PitchSequence // IsGoodTrack r }

def PitchSequence.new : PitchSequence := { intervals := [I.mk 0 1] : PitchSequence }

theorem PitchSequence.new.invariants : IsGoodTrack PitchSequence.new := {
  nontrvial := by
    simp [PitchSequence.new]
  intervalsDisjoint := by
    simp [PitchSequence.new]
}

def Track.new : Track := ⟨PitchSequence.new, PitchSequence.new.invariants⟩

def PitchSequence.length (t : PitchSequence) : Nat :=
  Nat.max 1 (t.intervals.map I.length |>.foldl Nat.max 1)

structure RawContext where
  sequencer : RBMap Pitch PitchSequence Nat.instLinearOrder.compare

structure GoodContext (r : RawContext) : Prop where
  atLeastOnePitchTrack : r.sequencer.size > 0

def RawContext.getSequenceForPitch (c : RawContext) (n : Nat) : Pitch × PitchSequence :=
  (c.sequencer.toList.get! n) -- TODO: write this differently.

def RawContext.new : RawContext := {
    sequencer := RBMap.empty.insert 0 Track.new.val
}
theorem RawContext.new.invariants : GoodContext RawContext.new := {
  atLeastOnePitchTrack := by decide
}

@[export monodrone_new_context]
def newContext (_ : Unit) : RawContext := RawContext.new

-- number of tracks in the context.
@[export monodrone_context_num_pitches]
def context_num_pitches (c : @&RawContext) : UInt32 :=
  c.sequencer.size.toUInt32

-- get the value of a pitch in the context.
def context_pitch_get (c : RawContext) (pitchix : UInt32) : UInt32 :=
  let pitch := c.getSequenceForPitch pitchix.toNat |>.fst
  pitch.toUInt32

-- number of intervals for a given pitch
def context_pitch_get_num_intervals (c : RawContext) (pitchix : UInt32) : UInt32 :=
  let seq := c.getSequenceForPitch pitchix.toNat |>.snd
  seq.intervals.length.toUInt32

-- get the start of an interval for a pitch.
def context_pitch_get_interval_start (c : RawContext) (pitchix : UInt32) (intervalix : UInt32): UInt32  :=
  let seq := c.getSequenceForPitch pitchix.toNat |>.snd
  0
  -- let i : I := seq.intervals.get! intervalix.toNat
  -- i.fst.toUInt32

-- get the end (inclusive) of an interval for a pitch.
def context_pitch_get_interval_end (c : RawContext) (pitchix : UInt32) (intervalix : UInt32): UInt32  :=
  let seq := c.getSequenceForPitch pitchix.toNat |>.snd
  0
  -- let i : I := seq.intervals.get! intervalix.toNat
  -- i.snd.toUInt32
