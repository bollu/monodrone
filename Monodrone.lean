import Lean
import Mathlib.Order.Interval.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Lemmas
import Mathlib.Data.Bool.AllAny
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
  pitch : Nat
  junk : Unit := () -- workaround for https://github.com/leanprover/lean4/issues/4278
deriving Inhabited, DecidableEq, Repr

def Pitch.middleC : Pitch := { pitch := 60 }
def Pitch.raiseSemitone (p : Pitch) : Pitch := { pitch := p.pitch + 1 }
def Pitch.lowerSemitone (p : Pitch) : Pitch := { pitch := (p.pitch - 1) }
def Pitch.raiseWhole (p : Pitch) : Pitch := { pitch := p.pitch + 2 }
def Pitch.lowerWhole (p : Pitch) : Pitch := { pitch := p.pitch - 2 }

def Note.lastNoteIx : Nat := 9999

structure Loc where
  x : Nat
  y : Nat
deriving DecidableEq, Repr, Inhabited

structure Span where
  topLeft : Loc
  width : Nat
  height : Nat
  hwidth : width > 0
  hheight : height > 0
deriving DecidableEq, Repr

def Loc.toSpan (l : Loc) : Span := {
  topLeft := l,
  width := 1,
  height := 1,
  hwidth := by decide,
  hheight := by decide
}

@[simp]
theorem topLeft_toSpan_eq (l : Loc) : l.toSpan.topLeft = l := rfl

def Span.bottomRight (s : Span) : Loc :=
  { x := s.topLeft.x + s.width - 1, y := s.topLeft.y + s.height - 1 }

instance : Inhabited Span where
  default := {
      topLeft := default,
      width := 1,
      height := 1,
      hwidth := by decide,
      hheight := by decide }
def Span.foldlLocs {α} (s : Span) (f : α → Loc → α) (a : α) : α :=
  List.foldl (λ a i => f a { x := s.topLeft.x + i % s.width, y := s.topLeft.y + i / s.width }) a (List.iota (s.width * s.height))

def Span.foldrLocs {α} (s : Span) (f : α → Loc → α) (a : α) : α :=
  List.foldr (λ i a => f a { x := s.topLeft.x + i % s.width, y := s.topLeft.y + i / s.width }) a (List.iota (s.width * s.height))

def Span.locs (s : Span) : List Loc :=
  Span.foldrLocs s (λ ls l => l :: ls) []

inductive Accidental
| natural
| sharp
| flat
deriving DecidableEq, Repr, Inhabited

inductive PitchName
| C
| D
| E
| F
| G
| A
| B
deriving DecidableEq, Repr, Inhabited


def PitchName.toUInt64 (p : PitchName) : UInt64 :=
  match p with
  | PitchName.C => 0
  | PitchName.D => 1
  | PitchName.E => 2
  | PitchName.F => 3
  | PitchName.G => 4
  | PitchName.A => 5
  | PitchName.B => 6

def PitchName.ofUInt64 (n : UInt64) : PitchName :=
  match n with
  | 0 => PitchName.C
  | 1 => PitchName.D
  | 2 => PitchName.E
  | 3 => PitchName.F
  | 4 => PitchName.G
  | 5 => PitchName.A
  | 6 => PitchName.B
  | _ => panic! s!"Invalid pitch name {n}"

/-- Our decoding is consistent with our encoding. -/
theorem PitchName.of_to_uint64 (p : PitchName) :
    PitchName.ofUInt64 p.toUInt64 = p := by
  cases p <;> rfl


/-- A piatch as shown to the user in the UI. -/
structure UserPitch where
  pitchName : PitchName
  accidental : Accidental
  octave : Nat
deriving DecidableEq, Repr

def UserPitch.toPitch (p : UserPitch) : Pitch :=
  let pitch := match p.pitchName with
  | PitchName.C => 0
  | PitchName.D => 2
  | PitchName.E => 4
  | PitchName.F => 5
  | PitchName.G => 7
  | PitchName.A => 9
  | PitchName.B => 11
  let pitch := (pitch : ℤ) + match p.accidental with
  | Accidental.natural => 0
  | Accidental.sharp => 1
  | Accidental.flat => -1
  let pitch := pitch + 12 * p.octave
  { pitch := pitch.toNat }

def UserPitch.toggleAccidental (p : UserPitch) (a : Accidental) : UserPitch :=
  { p with accidental := if p.accidental = a then Accidental.natural else a }

def UserPitch.raiseOctave (p : UserPitch) : UserPitch :=
  { p with octave := p.octave + 1 }

def UserPitch.lowerOctave (p : UserPitch) : UserPitch :=
  { p with octave := p.octave - 1 }

def UserPitch.middleC : UserPitch := {
  pitchName := PitchName.C,
  accidental := Accidental.natural,
  octave := 4
}

def UserPitch.ofPitchName (n : PitchName) : UserPitch := {
  pitchName := n,
  accidental := Accidental.natural,
  octave := 4
}

/-- A Note with a location. -/
structure Note where
  /-- the x axis location of the note. -/
  loc : Loc
  /-- the pitch of the note. -/
  userPitch : UserPitch
  /-- The duration of the note in steps. -/
  nsteps : Nat
  /-- a Note is played for at least one step -/
  hnsteps : nsteps > 0
deriving DecidableEq, Repr

instance : Inhabited Note where
  default := {
      userPitch := UserPitch.middleC,
      loc := default,
      nsteps := 1,
      hnsteps := by decide }

def Note.increaseNSteps (n : Note) : Note :=
  { n with nsteps := n.nsteps + 1, hnsteps := by omega }

def Note.decreaseSteps (n : Note) : Option Note :=
  if h : n.nsteps > 1 then
    some { n with nsteps := n.nsteps - 1, hnsteps := by omega }
  else none


def Note.atIx (ix : Loc) (n : PitchName) : Note :=
  { loc := ix, userPitch := UserPitch.ofPitchName n, nsteps := 1, hnsteps := by decide }

class Locable (α : Type) where
  toLoc : α → Loc
open Locable

class Spannable (α : Type) extends Locable α where
  toSpan : α → Span
  htoSpan : ∀ (a : α), toLoc a = (toSpan a).topLeft


instance : Locable Loc where
  toLoc l := l

instance : Spannable Span where
  toSpan s := s
  htoSpan _ := rfl
open Spannable

instance : Locable Note where
  toLoc n := n.loc

def Note.toSpan (n : Note) : Span :=
  { topLeft := n.loc,
    width := 1,
    height := n.nsteps,
    hwidth := by decide,
    hheight := n.hnsteps
  }

instance : Spannable Note where
  toSpan n := n.toSpan
  htoSpan _ := rfl

def Span.containsLoc (s : Span) (ix : Loc) : Prop :=
  ix.x ≥ s.topLeft.x && ix.x < s.topLeft.x + s.width &&
  ix.y ≥ s.topLeft.y && ix.y < s.topLeft.y + s.height

instance : Decidable (Span.containsLoc s ix) := by
  simp [Span.containsLoc]
  infer_instance

/-- disjoint iff disjoint in projection of x or projection of y. -/
def Span.disjoint (s t : Span) : Prop :=
  (s.topLeft.x + s.width ≤ t.topLeft.x) -- s ends before t starts in x axis.
  || (s.topLeft.x ≥ t.topLeft.x + t.width)  -- s starts after t ends in x axis.
  || (s.topLeft.y + s.height ≤ t.topLeft.y) -- s ends before t starts in y axis.
  || (s.topLeft.y ≥ t.topLeft.y + t.height) -- s starts after t ends in y axis

theorem Span.not_contains_loc_of_disjoint_of_contains_loc (s t : Span) (ix : Loc)
    (hst : Span.disjoint s t)
    (hs :  s.containsLoc ix) : ¬ t.containsLoc ix := by
  simp_all only [disjoint, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, containsLoc,
    ge_iff_le, not_and, not_lt, and_imp]
  intros hdisjoint hcontains
  rcases s with ⟨st, sw, sh, hsw, hsh⟩
  rcases t with ⟨tt, tw, th, htw, hth⟩
  rcases st with ⟨stx, sty⟩
  rcases tt with ⟨ttx, tty⟩
  simp_all
  omega

theorem Span.not_disjoint_of_contains_of_contains (s t : Span) (ix : Loc)
    (hs : s.containsLoc ix) (ht : t.containsLoc ix) : ¬ s.disjoint t := by
  simp_all [Span.disjoint, containsLoc]
  rcases s with ⟨st, sw, sh, hsw, hsh⟩
  rcases t with ⟨tt, tw, th, htw, hth⟩
  rcases st with ⟨stx, sty⟩
  rcases tt with ⟨ttx, tty⟩
  simp_all
  omega



theorem Span.disjoint_of_contains_iff_not_contains {s t: Span} {ix : Loc}
  (hix : s.containsLoc ix ↔ ¬ t.containsLoc ix) : s.disjoint t := by
  simp_all [Span.disjoint, Span.containsLoc]
  rcases s with ⟨st, sw, sh, hsw, hsh⟩
  rcases t with ⟨tt, tw, th, htw, hth⟩
  rcases st with ⟨stx, sty⟩
  rcases tt with ⟨ttx, tty⟩
  rcases ix with ⟨ixx, ixy⟩
  simp_all
  /-
  case mk.mk.mk.mk.mk.intro
  sw sh : ℕ
  hsw : sw > 0
  hsh : sh > 0
  tw th : ℕ
  htw : tw > 0
  hth : th > 0
  stx sty ttx tty ixx ixy : ℕ
  hix1 : ((stx ≤ ixx ∧ ixx < stx + sw) ∧ sty ≤ ixy) ∧ ixy < sty + sh → ttx ≤ ixx → ixx < ttx + tw → tty ≤ ixy → tty + th ≤ ixy
  hix2 : (ttx ≤ ixx → ixx < ttx + tw → tty ≤ ixy → tty + th ≤ ixy) → ((stx ≤ ixx ∧ ixx < stx + sw) ∧ sty ≤ ixy) ∧ ixy < sty + sh
  ⊢ (stx + sw ≤ ttx ∨ ttx + tw ≤ stx) ∨ sty + sh ≤ tty ∨ tty + th ≤ sty
  -/
  obtain ⟨hix1, hix2⟩ := hix
  try omega
  sorry

theorem Span.disjoint_irrefl (s : Span) : ¬ s.disjoint s := by
  simp [Span.disjoint]
  have := s.hwidth
  have := s.hheight
  omega

instance : Decidable (Span.disjoint s1 s2) := by
  simp [Span.disjoint]
  infer_instance

theorem Span.disjoint_symm (n1 n2 : Span) :
    Span.disjoint n1 n2 ↔ Span.disjoint n2 n1 := by
  simp [Span.disjoint]
  constructor <;> omega

def Span.overlaps (s1 s2 : Span) : Prop :=
  ¬ Span.disjoint s1 s2

theorem Span.overlaps_if_not_disjoint (n1 n2 : Span) :
    ¬ Span.disjoint n1 n2 → Span.overlaps n1 n2 := by
  simp [Span.disjoint, Span.overlaps]

theorem Span.disjoint_if_not_overlaps (n1 n2 : Span) :
    ¬ Span.overlaps n1 n2 → Span.disjoint n1 n2 := by
  simp [Span.disjoint, Span.overlaps]
  intros h₁
  omega

theorem Span.overlaps_symm (s t : Span) :
    Span.overlaps s t ↔ Span.overlaps t s := by
  simp [Span.overlaps, Span.disjoint]
  have := s.hheight
  have := s.hwidth
  have := t.hheight
  have := t.hwidth
  constructor <;> omega

def Span.containsSpan (s t : Span) : Prop :=
  s.topLeft.x ≤ t.topLeft.x && s.topLeft.y ≤ t.topLeft.y &&
  s.topLeft.x + s.width ≥ t.topLeft.x + t.width &&
  s.topLeft.y + s.height ≥ t.topLeft.y + t.height

instance : Decidable (Span.containsSpan s1 s2) := by
  simp [Span.containsSpan]
  infer_instance

theorem Span.containsSpan_refl (s : Span) : Span.containsSpan s s := by
  simp [Span.containsSpan]

theorem Span.containsSpan_eq_of_containSpan_constainsSpans (s t : Span)
  (hst : Span.containsSpan s t) (hts : Span.containsSpan t s) : s = t := by
  rcases s with ⟨st, sw, sh, hsw, hsh⟩
  rcases t with ⟨tt, tw, th, htw, hth⟩
  rcases st with ⟨stx, sty⟩
  rcases tt with ⟨ttx, tty⟩
  simp [Span.containsSpan] at *
  omega

theorem Span.containsSpan_transitive (s t u : Span)
    (hst : Span.containsSpan s t) (htu : Span.containsSpan t u) : Span.containsSpan s u := by
  simp [Span.containsSpan] at *
  omega

theorem Span.not_disjoint_of_containsSpan (s t : Span) :
   Span.containsSpan s t → ¬ s.disjoint t := by
  rcases s with ⟨st, sw, sh, hsw, hsh⟩
  rcases t with ⟨tt, tw, th, htw, hth⟩
  rcases st with ⟨stx, sty⟩
  rcases tt with ⟨ttx, tty⟩
  simp_all [Span.disjoint, Span.containsSpan]
  omega

theorem Span.overlaps_of_containsSpan (s t : Span) :
   Span.containsSpan s t → Span.overlaps s t := by
  simp [Span.overlaps]
  apply Span.not_disjoint_of_containsSpan

theorem Span.overlaps_of_containsSpan_symm (s t : Span) :
   Span.containsSpan s t → Span.overlaps t s := by
  simp [Span.overlaps, Span.containsSpan, Span.overlaps, Span.disjoint]
  rcases s with ⟨st, sw, sh, hsw, hsh⟩
  rcases t with ⟨tt, tw, th, htw, hth⟩
  rcases st with ⟨stx, sty⟩
  rcases tt with ⟨ttx, tty⟩
  simp_all
  omega

instance : Decidable (Span.overlaps s1 s2) := by
  simp [Span.overlaps]
  infer_instance

structure SpanY where
  x : Nat
  y : Nat
  height : Nat
  hheight : height > 0


def SpanY.toSpan (s : SpanY) : Span :=
  { topLeft := { x := s.x, y := s.y },
    width := 1,
    height := s.height,
    hwidth := by omega,
    hheight := s.hheight
  }

instance : Spannable SpanY where
  toLoc s := { x := s.x, y := s.y }
  toSpan := SpanY.toSpan
  htoSpan _ := rfl

instance : Inhabited SpanY where
  default := { x := 0, y := 0, height := 1, hheight := by omega }

def SpanY.bottom (s : SpanY) : Nat := s.y + s.height

def SpanY.containsLoc (s : SpanY) (ix : Loc) : Prop :=
  ix.x = s.x && ix.y ≥ s.y && ix.y < s.y + s.height

instance : Decidable (SpanY.containsLoc s ix) := by
  simp [SpanY.containsLoc]
  infer_instance


def Span.toSpanYs (s : Span) : List SpanY :=
  List.map (λ dx => {
    x := s.topLeft.x + dx,
    y := s.topLeft.y,
    height := s.height,
    hheight := s.hheight
  })
  (List.range s.width)



@[simp, note_omega]
def Note.start (n : Note) := n.loc.x

/-- The step when the note plays last. -/
@[note_omega]
def Note.lastPlayed (n : Note) : Nat := n.start + n.nsteps - 1

@[simp, note_omega]
def Note.disjoint (n1 n2 : Note) : Prop :=
  (toSpan n1).disjoint (toSpan n2)

/-- A track is a list of located notes, with all notes disjoint. -/
structure Track where
  notes : List Note
  hdisjoint : notes.Pairwise Note.disjoint
  junk : Unit := ()  -- workaround for https://github.com/leanprover/lean4/issues/4278
deriving Repr, DecidableEq

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

def Track.empty : Track := { notes := [], hdisjoint := by simp [] }

instance : Inhabited Track where
  default := Track.empty

inductive LocMoveAction
| up (d : Nat)
| down (d : Nat)
| left (d : Nat)
| right (d : Nat)

def LocMoveAction.act (c : Loc)
    (act : LocMoveAction) : Loc :=
  match act with
  | .up d => { c with y := c.y - d }
  | .down d => { c with y := c.y + d }
  | .left d => { c with x := c.x - d }
  | .right d => { c with x := c.x + d }

/-- Todo: show that moveDown / moveUp are a galois connection. -/

def Loc.moveDownOne (c : Loc) : Loc := (LocMoveAction.down 1).act c
def Loc.moveUpOne (c : Loc) : Loc := (LocMoveAction.up 1).act c
def Loc.moveLeftOne (c : Loc) : Loc := (LocMoveAction.left 1).act c
def Loc.moveRightOne (c : Loc) : Loc := (LocMoveAction.right 1).act c

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
deriving DecidableEq, Repr, Inhabited

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
  ninserts : Nat
  /- upon being applied to `cur`, gives previous element. -/
  historyPrev : List δ
  cur : α
   /- upon being applied, gives next element. -/
  historyNext: List δ
  -- hninserts : ninserts ≥ historyPrev.length + historyNext.length + 1
deriving Inhabited, Repr

instance [Repr α] [Repr δ] : Repr (HistoryStack α δ) where
  reprPrec h _ := "HistoryStack.mk " ++ repr h.historyPrev ++ " " ++ repr h.cur ++ " " ++ repr h.historyNext

def HistoryStack.init {α : Type} (a : α) : HistoryStack α δ where
  historyPrev := []
  cur := a
  historyNext := []
  ninserts := 1

def HistoryStack.prev (h : HistoryStack α δ) [Patchable α δ] : HistoryStack α δ :=
  match h.historyPrev with
  | [] => h
  | p :: ps =>
    let (next, patch) := Patchable.apply2 h.cur p
    { h with
      cur := next,
      historyPrev := ps,
      historyNext := patch :: h.historyNext,
      ninserts := h.ninserts + 1
    }

def HistoryStack.next (h : HistoryStack α δ) [Patchable α δ] : HistoryStack α δ :=
  match h.historyNext with
  | [] => h
  | a :: as =>
    let (next, patch) := Patchable.apply2 h.cur a
    {
      ninserts := h.ninserts + 1,
      cur := next,
      historyPrev := patch :: h.historyPrev,
      historyNext := as,
    }

/-- Todo: show that prev / next are a galois connection. -/
theorem HistoryStack.prev_next_eq_self_of_next_ne [Patchable α δ] [LawfulPatchable α δ]
    (h : HistoryStack α δ) (hprev : h.historyNext ≠ []) :
    (HistoryStack.prev (HistoryStack.next h)).cur = h.cur := by
  rcases h with ⟨ninserts, prev, cur, next⟩
  simp [HistoryStack.prev, HistoryStack.next]
  cases next <;> cases prev <;> simp_all

theorem HistoryStack.next_prev_eq_self_of_prev_ne [Patchable α δ] [LawfulPatchable α δ]
    (h : HistoryStack α δ)
    (hprev : h.historyPrev ≠ []) :
    (HistoryStack.next (HistoryStack.prev h)).cur = h.cur := by
  rcases h with ⟨ninserts, prev, cur, next⟩
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
  ninserts := h.ninserts + 1

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
  ninserts := h.ninserts + 1

/--  Undo will take us back to the previous state. -/
theorem HistoryStack.cur_prev_patchForgettingFuture_eq [DecidableEq α]
    [Diffable α δ] [LawfulDiffable α δ]
    (h : HistoryStack α δ) (patch : δ)  :
    (HistoryStack.patchForgettingFuture h patch).prev.cur = h.cur := by
  simp [HistoryStack.patchForgettingFuture, prev, next]

structure Selection where
  cursor : Loc -- Location of the cursor.
  selectAnchor : Option Loc -- Location where selection anchor was dropped.
deriving Inhabited, Repr, DecidableEq

def Selection.atbegin : Selection := { cursor := { x := 0, y := 0 }, selectAnchor := none }

def Selection.topLeft (s : Selection) : Loc :=
  match s.selectAnchor with
  | none => s.cursor
  | some a => { x := min a.x s.cursor.x, y := min a.y s.cursor.y }

def Selection.bottomRight (s : Selection) : Loc :=
  match s.selectAnchor with
  | none => s.cursor
  | some a => { x := max a.x s.cursor.x, y := max a.y s.cursor.y }

def Selection.toSpan (s : Selection) : Span :=
  { topLeft := s.topLeft,
    width := (s.bottomRight.x - s.topLeft.x) + 1,
    height := (s.bottomRight.y - s.topLeft.y) + 1,
    hwidth := by omega, hheight := by omega
  }

def Selection.selectAnchorLocMoveAct (s : Selection) (act : LocMoveAction) : Selection :=
  let anchor := s.selectAnchor.getD s.cursor
  { s with selectAnchor := act.act anchor }

def Selection.cursorMoveAct (s : Selection) (act : LocMoveAction) : Selection :=
  { s with cursor := act.act s.cursor, selectAnchor := .none }

instance : Spannable Selection where
  toSpan s := s.toSpan
  htoSpan _ := rfl

def Selection.ofSpan (s : Span) : Selection :=
  { cursor := s.topLeft, selectAnchor := s.bottomRight }

def Note.atSpanY (p : PitchName) (s : SpanY) : Note :=
  { loc := { x := s.x, y := s.y },
    userPitch := UserPitch.ofPitchName p,
    nsteps := s.height,
    hnsteps := s.hheight }


def Track.addNoteAtLoc (t : Track) (p : PitchName) (l : Loc) : Track :=
  let newNote := Note.atIx l p
  let deletedNotes := t.notes.filter (fun n => n.loc ≠ l)
  { t with notes := newNote :: deletedNotes, hdisjoint := sorry }

/--
If we have notes that overlap, then adjust their pitches.
If we have no notes that overlap, then add a new note into the span Y with the given pitch.
-/
def Track.addNoteAtSpanY (t : Track) (p : PitchName) (s : SpanY) : Track :=
  let newNote := Note.atSpanY p s -- insert new note.
  let deletedNotes := -- only keep those notes that are disjoint at the current span y.
    t.notes.filter (fun n =>
      (toSpan n).disjoint (toSpan s)
    )
  { t with notes := newNote :: deletedNotes, hdisjoint := sorry }

/--
For each Y axis span in the given span,
add a note with the given pitch if the span is empty,
and otherwise, adjust the pitch of the notes in the span.
-/
def Track.addNotesAtSpan (t : Track) (p : PitchName) (s : Span) : Track :=
  s.toSpanYs.foldl (fun t sy => t.addNoteAtSpanY p sy) t

def Track.modifyInSpan (t : Track) (s : Span) (f : Note → Option Note) : Track :=
  let modifiedNotes :=
    t.notes.foldl (fun ns n =>
      if s.containsSpan (toSpan n)
      then
        match f n with
        | none => ns
        | some n' => n' :: ns
      else n :: ns
    ) []
  { t with notes := modifiedNotes, hdisjoint := sorry }

/-- Set the pitch for each note in the span -/
def Track.setPitchAtSpan (t : Track) (p : PitchName) (s : Span) : Track :=
  t.modifyInSpan s (fun n =>
    .some { n with
      userPitch := { n.userPitch with pitchName := p }
    })

def Track.deleteNotesAtLoc (t : Track) (l : Loc) : Track :=
  let modifiedNotes := t.notes.filter (fun n => ¬ (toSpan n).containsLoc l )
  -- let modifiedNotes := t.notes.filter (fun n => n.loc ≠ l)
  { t with notes := modifiedNotes, hdisjoint := sorry }

/-- Remove all notes that overlap with the span -/
def Track.deleteNotesAtSpan (t : Track) (s : Span) : Track :=
  t.modifyInSpan s (fun _ => none)

def Track.toggleAccidental (t : Track) (a : Accidental) (s : Span) : Track :=
  t.modifyInSpan s (fun n =>
    .some { n with
      userPitch := { n.userPitch with accidental := if n.userPitch.accidental = a then Accidental.natural else a }
    })

def Track.toggleSharp (t : Track) (s : Span) : Track :=
  t.toggleAccidental Accidental.sharp s

def Track.toggleFlat (t : Track) (s : Span) : Track :=
  t.toggleAccidental Accidental.flat s

def Track.increaseDuration (t : Track) (s : Span) : Track :=
  t.modifyInSpan s (fun n => .some (n.increaseNSteps))

def Track.decreaseDuration (t : Track) (s : Span) : Track :=
  t.modifyInSpan s (fun n => n.decreaseSteps)

structure Eased (α : Type) where
  cur : α
  desired : α
deriving Inhabited, Repr

def Eased.atDesired (d : α) : Eased α := { cur := d, desired := d }

def Eased.step [Add α] [Sub α] [HMul Float α α] (e : Eased α) : Eased α :=
  let rate := 0.01
  { cur := e.cur + rate * (e.desired - e.cur), desired := e.desired }

structure Clipboard where
  notes : List Note
deriving Inhabited, Repr

def Clipboard.empty : Clipboard := { notes := [] }

structure RawContext where
  track : HistoryStack Track (NaiveDiff Track)
  clipboard : Clipboard
  cursor : HistoryStack Selection (NaiveDiff Selection)
  renderX : Eased Float
  renderY : Eased Float
  junk : Unit := () -- Workaround for: 'https://github.com/leanprover/lean4/issues/4278'
deriving Inhabited, Repr

def Track.copy (t : Track) (s : Selection) : Clipboard :=
  { notes := t.notes.filter (fun n => (toSpan n).containsLoc s.cursor) }

instance : Add Loc where
  add l1 l2 := { x := l1.x + l2.x, y := l1.y + l2.y }

def Track.paste (t : Track) (l : Loc) (c : Clipboard) : Track :=
  let newNotes := c.notes.map (fun n =>
    { n with loc := l + n.loc, hnsteps := n.hnsteps }
  )
  -- delete any notes that create overlaps.
  let deletedNotes := t.notes.filter (fun n => c.notes.any (fun n' => n.loc = n'.loc))
  { t with notes := newNotes ++ deletedNotes, hdisjoint := sorry }

def Track.cut (t : Track) (s : Selection) : Clipboard × Track :=
  let c := t.copy s
  let t := t.deleteNotesAtSpan s.toSpan
  (c, t)

def RawContext.empty : RawContext := {
    track := HistoryStack.init Track.empty,
    clipboard := Clipboard.empty,
    cursor := HistoryStack.init Selection.atbegin,
    renderX := Eased.atDesired 0.0,
    renderY := Eased.atDesired 0.0,
}

def RawContext.step (ctx : RawContext) : RawContext :=
  { ctx with
    track := ctx.track.next,
    cursor := ctx.cursor.next,
    renderX := ctx.renderX.step,
    renderY := ctx.renderY.step
  }

section ffi
/-!

#### C FFI

₂

We follow [json-c](https://json-c.github.io/json-c/json-c-0.17/doc/html/json__object_8h.html) naming conventions:

- `monodrone_` prefix
- `object_<type>_length` to count the number of elements in an object of type <type>
- `object_get_<type>` to get an element of type <type>
-/

/-# Ctx -/
@[export monodrone_ctx_new]
def newContext (_ : Unit) : RawContext := RawContext.empty

/-# Cursor Movement. -/

@[export monodrone_ctx_cursor_move_down_one]
def RawContext.moveDownOne (ctx : @&RawContext) : RawContext :=
  { ctx with cursor := ctx.cursor.modifyForgettingFuture fun s =>
    s.cursorMoveAct (LocMoveAction.down 1)
  }

@[export monodrone_ctx_cursor_move_up_one]
def RawContext.moveUpOne (ctx : @&RawContext) : RawContext :=
  { ctx with cursor := ctx.cursor.modifyForgettingFuture fun s =>
    s.cursorMoveAct (LocMoveAction.up 1)
  }

@[export monodrone_ctx_cursor_move_left_one]
def RawContext.moveLeftOne (ctx : @&RawContext) : RawContext :=
  { ctx with cursor := ctx.cursor.modifyForgettingFuture fun s =>
    s.cursorMoveAct (LocMoveAction.left 1)
  }

@[export monodrone_ctx_cursor_move_right_one]
def RawContext.moveRightOne (ctx : @&RawContext) : RawContext :=
  { ctx with cursor := ctx.cursor.modifyForgettingFuture fun s =>
    s.cursorMoveAct (LocMoveAction.right 1)
  }

@[export monodrone_ctx_select_anchor_move_left_one]
def RawContext.moveSelectAnchorLeftOne (ctx : @&RawContext) : RawContext :=
  { ctx with cursor := ctx.cursor.modifyForgettingFuture fun s =>
    s.selectAnchorLocMoveAct (LocMoveAction.left 1)
  }

@[export monodrone_ctx_select_anchor_move_right_one]
def RawContext.moveSelectAnchorRightOne (ctx : @&RawContext) : RawContext :=
  { ctx with cursor := ctx.cursor.modifyForgettingFuture fun s =>
    s.selectAnchorLocMoveAct (LocMoveAction.right 1)
  }

@[export monodrone_ctx_select_anchor_move_up_one]
def RawContext.moveSelectAnchorUpOne (ctx : @&RawContext) : RawContext :=
  { ctx with cursor := ctx.cursor.modifyForgettingFuture fun s =>
    s.selectAnchorLocMoveAct (LocMoveAction.up 1)
  }

@[export monodrone_ctx_select_anchor_move_down_one]
def RawContext.moveSelectAnchorDownOne (ctx : @&RawContext) : RawContext :=
  { ctx with cursor := ctx.cursor.modifyForgettingFuture fun s =>
    s.selectAnchorLocMoveAct (LocMoveAction.down 1)
  }

/-# Note Editing. -/

@[export monodrone_ctx_set_pitch]
def RawContext.setPitch (ctx : @&RawContext) (p : UInt64) : RawContext :=
  { ctx with track :=
    ctx.track.modifyForgettingFuture fun t =>
      t.addNotesAtSpan (PitchName.ofUInt64 p) ctx.cursor.cur.toSpan
  }

@[export monodrone_ctx_delete]
def RawContext.delete (ctx : @&RawContext) : RawContext :=
  { ctx with track :=
    ctx.track.modifyForgettingFuture fun t =>
      t.deleteNotesAtSpan ctx.cursor.cur.toSpan
  }

@[export monodrone_ctx_increase_duration]
def RawContext.increaseDuration (ctx : @&RawContext) : RawContext :=
  { ctx with track :=
    ctx.track.modifyForgettingFuture fun t =>
      t.increaseDuration ctx.cursor.cur.toSpan
  }

@[export monodrone_ctx_decrease_duration]
def RawContext.decreaseDuration (ctx : @&RawContext) : RawContext :=
  { ctx with track :=
    ctx.track.modifyForgettingFuture fun t =>
      t.decreaseDuration ctx.cursor.cur.toSpan
  }

/-# Cursor Query -/
@[export monodrone_ctx_get_cursor_sync_index]
def getCursorSyncIndex (ctx : @&RawContext) : UInt64 := ctx.cursor.ninserts.toUInt64

@[export monodrone_ctx_get_cursor_x]
def getCursorX (ctx : @&RawContext) : UInt64 := ctx.cursor.cur.cursor.x.toUInt64

@[export monodrone_ctx_get_cursor_y]
def getCursorY (ctx : @&RawContext) : UInt64 := ctx.cursor.cur.cursor.y.toUInt64

/-# Selection Query -/

@[export monodrone_ctx_has_select_anchor]
def hasSelectAnchor (ctx : @&RawContext) : Bool :=
  ctx.cursor.cur.selectAnchor != none

@[export monodrone_ctx_get_select_anchor_x]
def getSelectAnchornX (ctx : @&RawContext) : UInt64 :=
  match ctx.cursor.cur.selectAnchor with
  | none => ctx.cursor.cur.cursor.x.toUInt64
  | some s => s.x.toUInt64

@[export monodrone_ctx_get_select_anchor_y]
def getSelectAnchorY (ctx : @&RawContext) : UInt64 :=
  match ctx.cursor.cur.selectAnchor with
  | none => ctx.cursor.cur.cursor.y.toUInt64
  | some s => s.y.toUInt64

/-# Track Query -/

@[export  monodrone_ctx_get_track_sync_index]
def getTrackSyncIndex (ctx : @&RawContext) : UInt64 := ctx.track.ninserts.toUInt64

@[export monodrone_ctx_get_track_length]
def getTrackLength (ctx : @&RawContext) : UInt64 := ctx.track.cur.notes.length.toUInt64

@[export monodrone_ctx_get_track_note]
def trackGetNote (ctx : @&RawContext) (ix : UInt64) : Note :=
  ctx.track.cur.notes.get! ix.toNat


/-# Note Query -/

@[export monodrone_note_get_pitch_name]
def noteGetPitchName (n : @&Note) : UInt64 :=
  n.userPitch.pitchName.toUInt64

def Accidental.toUInt64 (a : Accidental) : UInt64 :=
  match a with
  | Accidental.natural => 0
  | Accidental.sharp => 1
  | Accidental.flat => 2

def Accidental.ofUInt64 (n : UInt64) : Accidental :=
  match n.toNat with
  | 0 => Accidental.natural
  | 1 => Accidental.sharp
  | 2 => Accidental.flat
  | _ => Accidental.natural

theorem Accidental.of_to_uint64 (a : Accidental) :
    Accidental.ofUInt64 a.toUInt64 = a := by
  cases a <;> rfl

@[export monodrone_note_get_pitch_accidental]
def noteGetAccidental (n : @&Note) : UInt64 :=
  n.userPitch.accidental.toUInt64


@[export monodrone_note_get_x]
def noteGetX (n : @&Note) : UInt64 := n.loc.x.toUInt64

@[export monodrone_note_get_y]
def noteGetY (n : @&Note) : UInt64 := n.loc.y.toUInt64

@[export monodrone_note_get_nsteps]
def noteGetNsteps (n : @&Note) : UInt64 :=
  n.nsteps.toUInt64

/-# Undo Redo Action -/
@[export monodrone_ctx_undo_action]
def RawContext.undoAction (ctx : @&RawContext) : RawContext :=
  { ctx with track := ctx.track.prev }

@[export monodrone_ctx_redo_action]
def RawContext.redoAction (ctx : @&RawContext) : RawContext :=
  { ctx with track := ctx.track.next }

/-# Undo Redo Movement -/
@[export monodrone_ctx_undo_movement]
def RawContext.undoMovement (ctx : @&RawContext) : RawContext :=
  { ctx with cursor := ctx.cursor.prev }

@[export monodrone_ctx_redo_movement]
def RawContext.redoMovement (ctx : @&RawContext) : RawContext :=
  { ctx with cursor := ctx.cursor.next }
end ffi
