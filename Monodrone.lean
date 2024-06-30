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
import Monodrone.PaperAttrs
import Mathlib.Data.List.MinMax
import Lean.Data.Json.Basic
import Lean.Data.Json.Parser
import Lean.Data.Json.Printer
open Lean Meta
open Batteries

instance : ToJson Unit where
  toJson _ := Json.null

instance : FromJson Unit where
  fromJson? j := match j with
  | Json.null => Except.ok ()
  | _ => Except.error s!"expected null for unit, found {j}"


def jsonRoundtrip (α : Type) [Inhabited α] [FromJson α] [ToJson α] :=
    (fromJson? (toJson (default : α)) : Except String α)

def jsonRoundtrip' {α : Type} [Inhabited α] [FromJson α] [ToJson α] (a : α):=
    (fromJson? (toJson (a)) : Except String α)

/-
Step: The smallest unit of time in a sequencer. Each step can be assigned a sound.
Pattern: A sequence of steps forming a repeating musical phrase or loop.
Track: A sequence lane dedicated to a specific drum sound or instrument.
-/

/-- A pitch represented by the MIDI pitch value. -/
structure Pitch where
  pitch : Nat
  junk : Unit := () -- workaround for https://github.com/leanprover/lean4/issues/4278
deriving Inhabited, DecidableEq, Repr, ToJson, FromJson


def Pitch.middleC : Pitch := { pitch := 60 }
def Pitch.raiseSemitone (p : Pitch) : Pitch := { pitch := p.pitch + 1 }
def Pitch.lowerSemitone (p : Pitch) : Pitch := { pitch := (p.pitch - 1) }
def Pitch.raiseWhole (p : Pitch) : Pitch := { pitch := p.pitch + 2 }
def Pitch.lowerWhole (p : Pitch) : Pitch := { pitch := p.pitch - 2 }

def Note.lastNoteIx : Nat := 9999

structure Loc where
  x : Nat
  y : Nat
deriving DecidableEq, Repr, Inhabited, ToJson, FromJson



structure Span where
  topLeft : Loc
  width : Nat
  height : Nat
  hwidth : width > 0
  hheight : height > 0
deriving DecidableEq, Repr

axiom json_parsing_is_safe {p : Prop} : p

instance : FromJson Span where
  fromJson? j :=
    let data : Except String (Loc × Nat × Nat) := fromJson? j
    data.map fun (l, w, h) => {
        topLeft := l,
        width := w,
        height := h,
        hwidth := json_parsing_is_safe,
        hheight := json_parsing_is_safe
      }


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

def SpanY.topLeft (s : SpanY) : Loc := { x := s.x, y := s.y }

@[simp]
theorem SpanY.topLeft_toSpan_eq_topLeft (s : SpanY) : s.toSpan.topLeft = s.topLeft := rfl

instance : Inhabited SpanY where
  default := { x := 0, y := 0, height := 1, hheight := by omega }

def SpanY.bottom (s : SpanY) : Nat := s.y + s.height

def SpanY.containsLoc (s : SpanY) (ix : Loc) : Prop :=
  ix.x = s.x && ix.y ≥ s.y && ix.y < s.y + s.height

def SpanY.containsY (s : SpanY) (y : Nat) : Prop :=
  y ≥ s.y && y < s.y + s.height

@[aesop unsafe, note_omega]
def SpanY.containsSpanY (s t : SpanY) : Prop :=
  s.x = t.x && s.y ≤ t.y && s.y + s.height ≥ t.y + t.height

@[aesop safe, note_omega]
theorem SpanY.containsSpanY_refl (s : SpanY) : SpanY.containsSpanY s s := by
  simp [SpanY.containsSpanY]

theorem SpanY.containsSpanY_trans (s t u : SpanY)
    (hst : SpanY.containsSpanY s t) (htu : SpanY.containsSpanY t u) : SpanY.containsSpanY s u := by
  simp [SpanY.containsSpanY] at *
  omega

@[note_omega]
def SpanY.disjoint (s t : SpanY) : Prop :=
  s.x ≠ t.x || s.y + s.height ≤ t.y || t.y + t.height ≤ s.y

@[aesop unsafe 50% apply]
theorem SpanY.disjoint_of_contains {s s' t : SpanY} (hss' : s.containsSpanY s')
    (hst : s.disjoint t) : s'.disjoint t := by
  rcases s with ⟨sx, sy, sh, hsh⟩
  rcases s' with ⟨s'x, s'y, s'h, hsh'⟩
  rcases t with ⟨tx, ty, th, hth⟩
  simp_all [SpanY.disjoint, SpanY.containsSpanY]
  omega

-- @[aesop unsafe  apply]
theorem SpanY.disjoint_of_contains_of_contains {s s' t t' : SpanY}
    (hss' : s.containsSpanY s')
    (htt' : t.containsSpanY t')
    (hst : s.disjoint t) : s'.disjoint t' := by
  rcases s with ⟨sx, sy, sh, hsh⟩
  rcases s' with ⟨s'x, s'y, s'h, hsh'⟩
  rcases t with ⟨tx, ty, th, hth⟩
  rcases t' with ⟨t'x, t'y, t'h, hth'⟩
  simp_all [SpanY.disjoint, SpanY.containsSpanY]
  omega

@[aesop unsafe apply]
theorem SpanY.disjoint_comm {s t : SpanY} : s.disjoint t ↔ t.disjoint s := by
  simp [SpanY.disjoint]
  constructor <;> omega

instance : Decidable (SpanY.disjoint s1 s2) := by
  simp [SpanY.disjoint]
  infer_instance

instance : Decidable (SpanY.containsSpanY s1 s2) := by
  simp [SpanY.containsSpanY]
  infer_instance

instance : Decidable (SpanY.containsLoc s ix) := by
  simp [SpanY.containsLoc]
  infer_instance



def Loc.toSpanY (l : Loc) : SpanY := { x := l.x, y := l.y, height := 1, hheight := by decide }

@[simp]
theorem topLeft_toSpanY_eq (l : Loc) : l.toSpanY.topLeft = l := rfl

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
deriving DecidableEq, Repr, Inhabited, ToJson, FromJson

inductive PitchName
| C
| D
| E
| F
| G
| A
| B
deriving DecidableEq, Repr, Inhabited, ToJson, FromJson


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
deriving DecidableEq, Repr, ToJson, FromJson, Inhabited

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
  octave := 3 -- middle C is 60 in MIDI pitch, which is 6 * (12 = length of scale in semitones).
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

instance : ToJson Note where
  toJson o :=
    let data : Loc × UserPitch × Nat := (o.loc, o.userPitch, o.nsteps)
    toJson data

instance : FromJson Note where
  fromJson? j :=
    let data : Except String (Loc × UserPitch × Nat) := fromJson? j
    data.map fun (l, p, n) => {
        loc := l,
        userPitch := p,
        nsteps := n,
        hnsteps := json_parsing_is_safe
      }

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

def Note.decreaseSteps' (n : Note) (hn : n.nsteps > 1 := by aesop): Note :=
    { n with nsteps := n.nsteps - 1, hnsteps := by omega }


def Note.setPitchName (n : Note) (p : PitchName) : Note :=
  { n with userPitch := { n.userPitch with pitchName := p } }

def Note.atIx (ix : Loc) (n : PitchName) : Note :=
  { loc := ix, userPitch := UserPitch.ofPitchName n, nsteps := 1, hnsteps := by decide }

class Locable (α : Type) where
  toLoc : α → Loc
open Locable

class Spannable (α : Type) extends Locable α where
  toSpan : α → Span
  htoSpan : ∀ (a : α), toLoc a = (toSpan a).topLeft

@[aesop unsafe unfold, note_omega]
def Note.toSpanY (n : Note) : SpanY :=
  { x := n.loc.x, y := n.loc.y, height := n.nsteps, hheight := n.hnsteps }

instance : Spannable SpanY where
  toLoc s := { x := s.x, y := s.y }
  toSpan := SpanY.toSpan
  htoSpan _ := rfl

instance : Locable Loc where
  toLoc l := l

instance : Spannable Span where
  toSpan s := s
  htoSpan _ := rfl
open Spannable

instance : Locable Note where
  toLoc n := n.loc

-- def Note.toSpan (n : Note) : Span :=
--   { topLeft := n.loc,

-- instance : Spannable Note where
--   toSpan n := n.toSpan
--   htoSpan _ := rfl

@[note_omega]
def Span.containsLoc (s : Span) (ix : Loc) : Prop :=
  ix.x ≥ s.topLeft.x && ix.x < s.topLeft.x + s.width &&
  ix.y ≥ s.topLeft.y && ix.y < s.topLeft.y + s.height

instance : Decidable (Span.containsLoc s ix) := by
  simp [Span.containsLoc]
  infer_instance

/-- disjoint iff disjoint in projection of x or projection of y. -/
@[note_omega]
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

@[note_omega]
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

@[note_omega]
def Span.containsSpan (s t : Span) : Prop :=
  s.topLeft.x ≤ t.topLeft.x && s.topLeft.y ≤ t.topLeft.y &&
  s.topLeft.x + s.width ≥ t.topLeft.x + t.width &&
  s.topLeft.y + s.height ≥ t.topLeft.y + t.height

theorem Span.topLeft_le_topLeft_of_containsSpan {s t : Span} (h : Span.containsSpan s t) :
    s.topLeft.x ≤ t.topLeft.x ∧ s.topLeft.y ≤ t.topLeft.y := by
  simp [Span.containsSpan] at h
  omega

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


def Span.toSpanYs (s : Span) : List SpanY :=
  List.map (λ dx => {
    x := s.topLeft.x + dx,
    y := s.topLeft.y,
    height := s.height,
    hheight := s.hheight
  })
  (List.range s.width)


/-`spany.splitBeforeY y = (s1, s2)` where
  `s1` is the span of all the elements in `s` that are strictly before `y` (excluding `y`)
  `s2` is the span of all the elements in `s` that are at and after `y` (≥ y). -/
def SpanY.splitBeforeY (s : SpanY) (y : Nat) : Option SpanY × Option SpanY :=
  if hbefore : y ≤ s.y then
    (none, some s)
  else if hafter : y ≥ s.y + s.height then
    (some s, none)
  else
    let sbefore :=
      { s with height := y - s.y, hheight := by omega }
    let safter :=
      { s with y := y, height := s.y + s.height - y, hheight := by omega }
    (some sbefore, some safter)

/-- if we get a 'fst', then it is contained in the original note. -/
@[aesop safe forward]
theorem SpanY.contains_of_splitBeforeY_fst {s top : SpanY} {y : Nat}
    {htop : (s.splitBeforeY y).fst = top} : s.containsSpanY top := by
  rcases s with ⟨sx, sy, sh, hsh⟩
  simp_all only [splitBeforeY, ge_iff_le]
  by_cases h : y ≤ sy
  · simp_all [h]
  · simp_all only [dite_false, not_le]
    by_cases h' : sy + sh ≤ y
    · simp_all only [dite_true, Option.some.injEq]
      subst htop
      simp [containsSpanY]
    · simp_all only [dite_false, Option.some.injEq, not_le]
      subst htop
      simp [containsSpanY]; omega


@[aesop safe forward]
theorem SpanY.disjoint_of_splitBeforeY {s top bot : SpanY} {y : Nat}
    {htop : top ∈ (s.splitBeforeY y).fst}
    {hbot : bot ∈ (s.splitBeforeY y).snd} : top.disjoint bot := by
  rcases s with ⟨sx, sy, sh, hsh⟩
  simp_all only [splitBeforeY, ge_iff_le]
  by_cases h : y ≤ sy
  · simp_all [h]
  · simp_all [h]
    by_cases h' : sy + sh ≤ y
    · simp_all [h']
    · simp_all [h']
      subst hbot
      subst htop
      simp [disjoint]; omega

@[aesop safe forward]
theorem SpanY.y_lt_y_of_splitBeforeY {s top bot : SpanY} {y : Nat}
    {htop : top ∈ (s.splitBeforeY y).fst}
    {hbot : bot ∈ (s.splitBeforeY y).snd} : top.y < bot.y := by
  rcases s with ⟨sx, sy, sh, hsh⟩
  simp_all only [splitBeforeY, ge_iff_le]
  by_cases h : y ≤ sy
  · simp_all [h]
  · simp_all [h]
    by_cases h' : sy + sh ≤ y
    · simp_all [h']
    · simp_all [h']
      subst hbot
      subst htop
      simp
      omega


/-- if we get a 'snd', then it is contained in the original note. -/
@[simp, aesop safe forward]
theorem SpanY.contains_of_splitBeforeY_snd {s bot : SpanY} {y : Nat}
    {hbot : (s.splitBeforeY y).snd = bot} : s.containsSpanY bot := by
  rcases s with ⟨sx, sy, sh, hsh⟩
  simp_all only [splitBeforeY, ge_iff_le]
  by_cases h : y ≤ sy
  · simp_all [h]
    subst hbot
    simp [containsSpanY]
  · simp_all [h]
    by_cases h' : sy + sh ≤ y
    · simp_all [h']
    · simp_all only [dite_false, Option.some.injEq, not_le]
      subst hbot
      simp [containsSpanY]; omega

def Note.ofSpanY (s : SpanY) (p : UserPitch) : Note :=
  { loc := { x := s.x, y := s.y },
    userPitch := p,
    nsteps := s.height,
    hnsteps := s.hheight
  }

@[simp]
theorem Note.toSpanY_ofSpanY_eq :
    (Note.ofSpanY s p).toSpanY = s := by
  simp [Note.ofSpanY, Note.toSpanY]

def Note.splitBeforeY (n : Note) (y : Nat) : Option Note × Option Note :=
  let s := n.toSpanY
  match s.splitBeforeY y with
  | (none, none) => (none, none)
  | (none, some s2) => (none, Note.ofSpanY s2 n.userPitch)
  | (some s1, none) => (Note.ofSpanY s1 n.userPitch, none)
  | (some s1, some s2) =>
    (Note.ofSpanY s1 n.userPitch, Note.ofSpanY s2 n.userPitch)

@[simp, aesop safe forward]
theorem Note.elim_splitBeforeY_eq_none_none {n : Note} {y : Nat}
      (h : n.splitBeforeY y = (none, none)) : False := by
  rcases n with ⟨l, p, ns, hns⟩
  rcases l with ⟨lx, ly⟩
  simp [Note.splitBeforeY, Note.toSpanY, SpanY.splitBeforeY] at h
  by_cases hy : y ≤ ly <;> simp_all [hy]
  split_ifs at h <;> simp_all

@[aesop safe forward]
theorem Note.contains_of_splitBeforeY_snd {n bot : Note} {y : Nat}
    (hbot : (n.splitBeforeY y).snd = bot) : n.toSpanY.containsSpanY bot.toSpanY := by
  simp [Note.splitBeforeY] at hbot
  rcases hn : n.toSpanY.splitBeforeY y with ⟨s1, s2⟩
  rcases s1 with rfl | s1 <;> rcases s2 with rfl | s2 <;> simp_all
  repeat (apply SpanY.contains_of_splitBeforeY_snd; rw [hn]; simp [← hbot])

@[aesop safe forward]
theorem Note.contains_of_splitBeforeY_fst {n top : Note} {y : Nat}
    (htop : (n.splitBeforeY y).fst = top) : n.toSpanY.containsSpanY top.toSpanY := by
  simp [Note.splitBeforeY] at htop
  rcases hn : n.toSpanY.splitBeforeY y with ⟨s1, s2⟩
  rcases s1 with rfl | s1 <;> rcases s2 with rfl | s2 <;> simp_all
  repeat (apply SpanY.contains_of_splitBeforeY_fst; rw [hn]; simp[← htop])

@[aesop safe forward]
theorem Note.disjoint_of_splitBeforeY {n top bot : Note} {y : Nat}
    (htop : (n.splitBeforeY y).fst = top)
    (hbot : (n.splitBeforeY y).snd = bot) : top.toSpanY.disjoint bot.toSpanY := by
  simp [Note.splitBeforeY] at htop hbot
  rcases hn : n.toSpanY.splitBeforeY y with ⟨s1, s2⟩
  rcases s1 with rfl | s1 <;> rcases s2 with rfl | s2 <;> simp_all
  subst htop hbot
  apply SpanY.disjoint_of_splitBeforeY <;> rw[hn] <;> simp

@[aesop safe forward]
theorem Note.y_lt_y_of_splitBeforeY {n top bot : Note} {y : Nat}
    (htop : (n.splitBeforeY y).fst = top)
    (hbot : (n.splitBeforeY y).snd = bot) : top.loc.y < bot.loc.y := by
  simp [Note.splitBeforeY] at htop hbot
  rcases hn : n.toSpanY.splitBeforeY y with ⟨s1, s2⟩
  rcases s1 with rfl | s1 <;> rcases s2 with rfl | s2 <;> simp_all
  subst htop hbot
  apply SpanY.y_lt_y_of_splitBeforeY <;> rw [hn] <;> simp

@[simp, note_omega]
def Note.start (n : Note) := n.loc.x

/-- The step when the note plays last. -/
@[note_omega]
def Note.lastPlayed (n : Note) : Nat := n.start + n.nsteps - 1

@[simp, note_omega, aesop unsafe unfold]
def Note.disjoint (n1 n2 : Note) : Prop :=
  (toSpanY n1).disjoint (n2.toSpanY)

theorem Note.disjoint_comm (n1 n2 : Note) :
    n1.disjoint n2 ↔ n2.disjoint n1 := by
  simp [Note.disjoint]
  apply SpanY.disjoint_comm

/-- A track is a list of located notes, with all notes disjoint. -/
structure Track where
  notes : List Note
  hdisjoint : notes.Pairwise Note.disjoint
  junk : Unit := ()  -- workaround for https://github.com/leanprover/lean4/issues/4278
deriving Repr, DecidableEq

instance : ToJson Track where
  toJson o := toJson o.notes

instance : FromJson Track where
  fromJson? j := do
    let data : Except String (List Note) := fromJson? j
    data.map fun notes => {
        notes := notes,
        hdisjoint := json_parsing_is_safe
    }

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

open List in
theorem List.pairwise_filter_of_pairwise_self {l : List α} {R : α → α → Prop}
    {hl : List.Pairwise R l} : (l.filter p).Pairwise R := by
  induction l
  case nil => simp
  case cons a as ih =>
    simp [filter]
    simp_all only [pairwise_cons, true_implies]
    cases p a <;> simp only [ih]
    rw [List.pairwise_cons]
    simp [ih, hl]
    intros a' ha'
    apply hl.1
    apply List.mem_of_mem_filter
    assumption

def Track.empty : Track := { notes := [], hdisjoint := by simp [] }

instance : Inhabited Track where
  default := Track.empty

inductive LocMoveAction
| up (d : Nat)
| down (d : Nat)
| left (d : Nat)
| right (d : Nat)
deriving ToJson, FromJson, Inhabited, Repr

def LocMoveAction.act (c : Loc)
    (act : LocMoveAction) : Loc :=
  match act with
  | .up d => { c with y := c.y - d }
  | .down d => { c with y := c.y + d }
  | .left d => { c with x := c.x - d }
  | .right d => { c with x := c.x + d }

/-- Todo: show that moveDown / moveUp are a galois connection. -/

def Loc.moveDownOne (c : Loc) : Loc := (LocMoveAction.down 1).act c
def Loc.moveDown (c : Loc) (nsteps : Nat) : Loc := (LocMoveAction.down nsteps).act c
def Loc.moveUpOne (c : Loc) : Loc := (LocMoveAction.up 1).act c
def Loc.moveUp (c : Loc) (nsteps : Nat) : Loc := (LocMoveAction.up nsteps).act c
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
deriving DecidableEq, Repr, Inhabited, ToJson, FromJson

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
deriving Inhabited, Repr, ToJson, FromJson


def HistoryStack.init {α : Type} (a : α) : HistoryStack α δ where
  historyPrev := []
  cur := a
  historyNext := []
  ninserts := 1

-- #eval (FromJson.fromJson? (toJson (Foo.init : Foo Float (NaiveDiff Float))) : Except String (Foo Float (NaiveDiff Float)))
-- #eval (FromJson.fromJson? (toJson (HistoryStack.init (40 : Float) (δ := NaiveDiff Float))) : Except String (HistoryStack Float (NaiveDiff Float)))


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
deriving Inhabited, Repr, DecidableEq, ToJson, FromJson

def Selection.atbegin : Selection := { cursor := { x := 0, y := 0 }, selectAnchor := none }

def Selection.topLeft (s : Selection) : Loc :=
  match s.selectAnchor with
  | none => s.cursor
  | some a => { x := min a.x s.cursor.x, y := min a.y s.cursor.y }

def Selection.bottomRight (s : Selection) : Loc :=
  match s.selectAnchor with
  | none => s.cursor
  | some a => { x := max a.x s.cursor.x, y := max a.y s.cursor.y }

@[simp, note_omega, aesop unsafe unfold]
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


@[simp]
theorem Note.atIx_toSpan_eq (l : Loc) (p : PitchName) :
    (Note.atIx l p).toSpanY = l.toSpanY := by
  simp [Note.toSpanY, Note.toSpanY, Note.atIx, Loc.toSpanY]

/-- TODO: figure out the right simp normal form? -/
@[simp]
theorem Loc.toSpan_disjoint {l : Loc} {s : SpanY} :
    l.toSpanY.disjoint s ↔ ¬ s.containsLoc l := by
  rcases l with ⟨lx, ly⟩
  rcases s with ⟨sx, sw, sh, hsw, hsh⟩ <;>
    simp [SpanY.disjoint, SpanY.containsLoc, Loc.toSpanY] <;> omega

def Track.addNoteAtLoc (t : Track) (p : PitchName) (l : Loc) : Track :=
  let collision? := t.notes.any (fun n => n.toSpanY.containsLoc l)
  let ns := t.notes.map (fun n => if n.toSpanY.containsLoc l then n.setPitchName p else n)
  let newNote := Note.atIx l p
  let ns := if collision? then ns else newNote :: t.notes
  { t with
    notes := ns,
    hdisjoint := by
      sorry -- TODO:
   }



@[simp]
theorem Note.toSpan_atSpanY (p : PitchName) (s : SpanY) :
    (Note.atSpanY p s).toSpanY = s := by
  simp [Note.atSpanY, Note.toSpanY]

/--
If we have notes that overlap, then adjust their pitches.
If we have no notes that overlap, then add a new note into the span Y with the given pitch.
-/
def Track.addNoteAtSpanY (t : Track) (p : PitchName) (s : SpanY) : Track :=
  let newNote := Note.atSpanY p s -- insert new note.
  let deletedNotes := -- only keep those notes that are disjoint at the current span y.
    t.notes.filter (fun n =>
      n.toSpanY.disjoint s
    )
  { t with
    notes := newNote :: deletedNotes,
    hdisjoint := by
      simp_all only [List.pairwise_cons, Note.disjoint, newNote, deletedNotes]
      constructor
      · intros n hn
        have hn' := List.of_mem_filter hn
        simp_all only [decide_eq_true_eq, Note.toSpan_atSpanY]
        rw [SpanY.disjoint_comm]
        assumption
      · apply List.pairwise_filter_of_pairwise_self
        exact t.hdisjoint
    }


/--
For each Y axis span in the given span,
add a note with the given pitch if the span is empty,
and otherwise, adjust the pitch of the notes in the span.
-/
def Track.addNotesAtSpan (t : Track) (p : PitchName) (s : Span) : Track :=
  s.toSpanYs.foldl (fun t sy => t.addNoteAtSpanY p sy) t



/-- Allow changing notes as long as the resulting note is always contained in the original note. -/
def Track.mapNotes_of_contains (t : Track) (f : Note → Note) (hf : ∀ (n : Note),  n.toSpanY.containsSpanY (f n).toSpanY) : Track :=
  { t with
    notes := t.notes.map f,
    hdisjoint := by
      apply List.pairwise_map' t.hdisjoint
      intros a b hab
      have hfa : a.toSpanY.containsSpanY (f a).toSpanY := hf a
      have hfb : b.toSpanY.containsSpanY (f b).toSpanY := hf b
      apply SpanY.disjoint_of_contains_of_contains hfa hfb hab
  }

/-- Map, while allowing to drop elements. -/
def List.map? {α β : Type} (f : α → Option β) : List α → List β
  | [] => []
  | a :: as =>
    match f a with
    | none => List.map? f as
    | some b => b :: List.map? f as

@[simp]
theorem List.map?_nil {α β : Type} (f : α → Option β) : List.map? f [] = [] := by
  simp [List.map?]

@[simp]
theorem List.map?_cons {α β : Type} (f : α → Option β) (a : α) (as : List α) :
    List.map? f (a :: as) = match f a with
    | none => List.map? f as
    | some b => b :: List.map? f as := by
  simp [List.map?]

/-  A member of `map?`, then we are guaranteed a preimage. -/
theorem List.mem?_map {α β : Type} {f : α → Option β} {b : β} {as : List α}
    (hb : b ∈ List.map? f as) : ∃ a', a' ∈ as ∧ b ∈ f a' := by
  induction as
  case nil => simp at hb
  case cons a as ih =>
    simp_all [List.map?]
    rcases hfa : f a with rfl | b'
    · simp_all [hfa]
    · simp_all [hfa]
      rcases hb with rfl | hb
      · simp
      · specialize (ih hb)
        right
        exact ih

theorem List.Pairwise_map?_of_pairwise {α β : Type} {R : α → α → Prop} {S : β → β → Prop}
    {l : List α} {f : α → Option β}
    (hf : ∀ {a a' : α} {b b' : β} {hb : b ∈ f a} {hb' : b' ∈ f a'} (haa' : R a a'), S b b')
    (hl : l.Pairwise R) : l.map? f |>.Pairwise S := by
  induction l
  case nil => simp [map?]
  case cons a as ih =>
    simp [List.map?]
    rcases hfa : f a with rfl | b <;> simp []
    · aesop
    · simp at hl
      simp [ih hl.2]
      intros b' hb'
      obtain ⟨a', ha'⟩ := List.mem?_map hb'
      apply hf (hl.1 _ ha'.1) <;> aesop

/-- Allow changing and potentially deleting notes as long as the new note is always in the old note.
This can be used to implement 'shrinkNote' in a clean way.
-/
def Track.mapNotes?_of_contains (t : Track) (f : Note → Option Note)
    (hf : ∀ (n fn : Note), fn ∈ (f n) → n.toSpanY.containsSpanY fn.toSpanY) : Track :=
  { t with
    notes := t.notes.map? f,
    hdisjoint := by
      rcases t with ⟨notes, hdisjoint, junk⟩
      simp
      apply List.Pairwise_map?_of_pairwise
      intros a a' b b' hb hb' hab
      simp [Note.disjoint]
      apply SpanY.disjoint_of_contains_of_contains
      · apply hf
        exact hb
      · apply hf
        exact hb'
      · assumption
      · apply hdisjoint
  }


/-- TODO: write proof by reflection. -/
def Track.modifyOverlapSpan (t : Track) (s : Span)
    (f : Note → Option Note)
    (hf : ∀ (n n' : Note) (s : Span) (hn : s.overlaps n.toSpanY.toSpan) (hn' : n' ∈ f n),
      n.toSpanY.containsSpanY n'.toSpanY := by aesop) : Track :=
  { t with
    notes := t.notes.map? (fun n => if s.overlaps n.toSpanY.toSpan then f n else n),
    hdisjoint := by
      rcases t with ⟨notes, hdisjoint, junk⟩
      simp
      apply List.Pairwise_map?_of_pairwise (hl := hdisjoint)
      intros a a' b b' hb hb'
      intros hr
      simp_all only [Note.disjoint]
      split_ifs at hb <;>
        split_ifs at hb' <;>
          simp_all [hb, hb'] <;> apply SpanY.disjoint_of_contains_of_contains
            <;> (try assumption)
      repeat (apply hf <;> assumption)
      repeat (apply SpanY.containsSpanY_refl)
      apply hf <;> assumption
  }

/-- info: 'Track.modifyOverlapSpan' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Track.modifyOverlapSpan

/- TODO: golf this proof more. -/
/- TODO: write proof by reflection for disjoint and contained goals. -/
def Track.modifyContainedInSpan (t : Track) (s : Span)
    (f : Note → Option Note)
    (hf : ∀ (n n' : Note) (s : Span) (hn : s.containsSpan n.toSpanY.toSpan) (hn' : n' ∈ f n),
      n.toSpanY.containsSpanY n'.toSpanY := by aesop) : Track :=
  { t with
    notes := t.notes.map? (fun n => if s.containsSpan n.toSpanY.toSpan then f n else n),
    hdisjoint := by
      rcases t with ⟨notes, hdisjoint, junk⟩
      simp
      apply List.Pairwise_map?_of_pairwise (hl := hdisjoint)
      intros a a' b b' hb hb'
      intros hr
      simp_all only [Note.disjoint]
      split_ifs at hb <;>
        split_ifs at hb' <;>
          simp_all [hb, hb'] <;> apply SpanY.disjoint_of_contains_of_contains
            <;> (try assumption)
      repeat (apply hf <;> assumption)
      repeat (apply SpanY.containsSpanY_refl)
      apply hf <;> assumption
  }

/--
info: 'Track.modifyContainedInSpan' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Track.modifyContainedInSpan

/-- Set the pitch for each note in the span -/
def Track.setPitchNameAtSpan (t : Track) (p : PitchName) (s : Span) : Track :=
  t.modifyOverlapSpan s (f := fun n =>
    .some { n with
      userPitch := { n.userPitch with pitchName := p }
    })

/-- Remove all notes that overlap with the span -/
def Track.deleteNotesContainedInSpan (t : Track) (s : Span) : Track :=
  t.modifyContainedInSpan s (f := fun _ => none)


/-- Toggle the accidental at the note. -/
def Track.toggleAccidental (t : Track) (a : Accidental) (s : Span) : Track :=
  t.modifyOverlapSpan s (f := fun n =>
    .some { n with
      userPitch := { n.userPitch with accidental := if n.userPitch.accidental = a then Accidental.natural else a }
    })

syntax "note_omega":tactic

macro_rules
| `(tactic| note_omega) =>
    `(simp_all[note_omega]
      omega)

-- TODO: write a note_omega tactic.
/-- Decrease the duration of the note. -/
def Track.decreaseDuration (t : Track) (s : Span) : Track :=
  t.modifyOverlapSpan s (f := fun n =>
    if hn : n.nsteps = 1
    then none
    else some { n with nsteps := n.nsteps - 1, hnsteps := by have hnsteps := n.hnsteps; omega })
    (hf := by
      intros n n' s hs hn'
      rcases n with ⟨nloc, npitch, nsteps, hnsteps⟩
      simp only [Option.mem_def, Option.some.injEq] at hn'
      by_cases hsteps : nsteps = 1
      · simp [hsteps] at hn'
      · simp [hsteps] at hn'
        rw [← hn']
        simp_all [note_omega])


-- /- This does not work since it does not work for reflexitve relations.
-- We need this to implement "cut all notes at this location."
-- -/

def List.concatMap {α β : Type} (f : α → List β) : List α → List β
  | [] => []
  | a :: as => f a ++ List.concatMap f as

/-  A member of `map?`, then we are guaranteed a preimage. -/
theorem List.mem?_concatMap {α β : Type} {f : α → List β} {b : β} {as : List α}
    (hb : b ∈ List.concatMap f as) : ∃ a', a' ∈ as ∧ b ∈ f a' := by
  induction as
  case nil => simp [concatMap] at hb
  case cons a as ih =>
    simp_all [List.map?]
    rcases hfa : f a with rfl | b'
    · simp_all [hfa]
      simp [concatMap] at hb
      rcases hb with hb | hb
      · simp [hfa] at hb
      · apply ih hb
    · simp_all [hfa]
      simp [concatMap] at hb
      rcases hb with hb | hb
      · simp_all
      · specialize (ih hb)
        right
        exact ih

/-- Ask Alex what the correct coineuctive theorem statement is. -/
theorem List.pairwise_concatMap_of_pairwise {α β : Type} {R : α → α → Prop} {S : β → β → Prop}
    {l : List α} {f : α → List β}
    (hfintra : ∀ {a : α}, Pairwise S (f a))
    (hfinter : ∀ {a a' : α} {b b' : β} (hb : b ∈ f a) (hb' : b' ∈ f a') (hr : R a a'), S b b')
    (hl : l.Pairwise R) : l.concatMap f |>.Pairwise S := by
  induction l
  case nil => simp [List.concatMap]
  case cons a as ih =>
    simp only [pairwise_cons] at hl
    simp only [concatMap, pairwise_append, hfintra, ih hl.2, true_and]
    intros b hb b' hb'
    obtain ⟨a', ha', hb'⟩ := List.mem?_concatMap hb'
    apply hfinter
    · exact hb
    · exact hb'
    · apply hl.1
      apply ha'

structure Eased (α : Type) where
  cur : α
  desired : α
deriving Inhabited, Repr, ToJson, FromJson

def Eased.atDesired (d : α) : Eased α := { cur := d, desired := d }

def Eased.step [Add α] [Sub α] [HMul Float α α] (e : Eased α) : Eased α :=
  let rate := 0.01
  { cur := e.cur + rate * (e.desired - e.cur), desired := e.desired }

structure Clipboard where
  notes : List Note
deriving Inhabited, Repr, ToJson, FromJson

def Clipboard.empty : Clipboard := { notes := [] }


structure SequenceNumbered (α : Type) where
  val : α
  sequenceNumber : Nat
  junk : Unit := ()
deriving Inhabited, Repr, ToJson, FromJson

def SequenceNumbered.new (val : α) : SequenceNumbered α :=
  { val := val, sequenceNumber := 42 }

def SequenceNumbered.modify (s : SequenceNumbered α) (f : α → α) : SequenceNumbered α :=
  { s with val := f s.val, sequenceNumber := s.sequenceNumber + 1 }

def SequenceNumbered.get (s : SequenceNumbered α) : α := s.val

instance : Coe (SequenceNumbered α) α where
  coe s := s.val

structure RawContext where
  playbackSpeed : SequenceNumbered Float
  filepath : String
  track : HistoryStack Track (NaiveDiff Track)
  clipboard : Clipboard
  cursor : HistoryStack Selection (NaiveDiff Selection)
  artist_name : String
  track_name : String
  time_signature : Nat × Nat
  junk : Unit := () -- Workaround for: 'https://github.com/leanprover/lean4/issues/4278'
deriving Inhabited, Repr, ToJson, FromJson


@[simp]
theorem Note.topLeft_toSpanY_eq_loc (n : Note) :
    n.toSpanY.topLeft = n.loc := by aesop

def Loc.sub (l : Loc) (delta : Loc) (hl : l.x ≥ delta.x ∧ l.y ≥ delta.y := by aesop) : Loc :=
  { x := l.x - delta.x, y := l.y - delta.y }

/--
Copy the notes into the clipboard.
In the clipboard, the notes are copied relative to the clipboard coordinate system.
-/
def Track.copy (t : Track) (s : Selection) : Clipboard :=
  let ns := t.notes.map? (fun n =>
    if hn : s.toSpan.containsSpan n.toSpanY.toSpan
    then some {
      n with loc := n.loc.sub s.topLeft (by
        have hn' := Span.topLeft_le_topLeft_of_containsSpan hn
        simp at hn'
        omega
      )
    }
    else none)
  { notes := ns }

instance : Add Loc where
  add l1 l2 := { x := l1.x + l2.x, y := l1.y + l2.y }


def Track.cut (t : Track) (s : Selection) : Clipboard × Track :=
  let c := t.copy s
  let t := t.deleteNotesContainedInSpan s.toSpan
  (c, t)

def RawContext.step (ctx : RawContext) : RawContext :=
  { ctx with
    track := ctx.track.next,
    cursor := ctx.cursor.next,
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
def newContext (filepath : String) : RawContext := {
    track := HistoryStack.init Track.empty,
    clipboard := Clipboard.empty,
    cursor := HistoryStack.init Selection.atbegin,
    filepath := filepath,
    playbackSpeed := SequenceNumbered.new 0.5
    time_signature := (4, 4),
    artist_name := "Monodrone",
    track_name := "Untitled"
}

/- # Filepath -/
def monodrone_ctx_set_file_path (ctx : @&RawContext) (filepath : String) : RawContext :=
  { ctx with filepath := filepath }
def monodrone_ctx_get_file_path (ctx : @&RawContext) : String := ctx.filepath

/- # Playback Speed -/

@[export monodrone_ctx_get_playback_speed]
def monodrone_ctx_get_playback_speed (ctx : @&RawContext) : Float :=
  ctx.playbackSpeed

@[export monodrone_ctx_set_playback_speed]
def monodrone_ctx_set_playback_speed (ctx : @&RawContext) (val : Float) : RawContext :=
  { ctx with playbackSpeed := SequenceNumbered.new val }

@[export monodrone_ctx_decrease_playback_speed]
def monodrone_ctx_decrease_playback_speed (ctx : @&RawContext) : RawContext :=
  { ctx with playbackSpeed := ctx.playbackSpeed.modify (fun v => (v - 0.2)) }

@[export monodrone_ctx_increase_playback_speed]
def monodrone_ctx_increase_playback_speed (ctx : @&RawContext) : RawContext :=
  { ctx with playbackSpeed := ctx.playbackSpeed.modify (fun v => (v + 0.2)) }

@[export monodrone_ctx_get_playback_speed_sequence_number]
def monodrone_ctx_get_playback_speed_sequence_number (ctx : @&RawContext) : UInt64 :=
  ctx.playbackSpeed.sequenceNumber.toUInt64

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



def Note.moveDownOne (n : Note) : Note :=
  { n with loc := n.loc.moveDownOne }

def Note.moveDown (n : Note) (nsteps : Nat ): Note :=
  { n with loc := n.loc.moveDown nsteps }

def Note.moveDownOne_disjoint_of_disjoint_of_le {n m : Note}
    (hnm : n.loc.y ≤ m.loc.y)
    (hdisjoint : n.toSpanY.disjoint m.toSpanY) :
    n.toSpanY.disjoint (Note.moveDownOne m).toSpanY := by
  rcases n with ⟨nloc, npitch, n_nsteps, n_hnsteps⟩
  rcases m with ⟨mloc, mpitch, m_nsteps, n_msteps⟩
  rcases nloc with ⟨nx, ny⟩
  rcases mloc with ⟨mx, my⟩
  simp_all [moveDownOne, disjoint, toSpanY, SpanY.disjoint, moveDownOne,
    Loc.moveDownOne, LocMoveAction.act]
  omega

def Note.moveUpOne (n : Note) : Note :=
  { n with loc := n.loc.moveUpOne }

def Note.moveUp (n : Note) (nsteps : Nat): Note :=
  { n with loc := n.loc.moveUp nsteps }


def Track.splitBeforeYAux (y : Nat) (ns : List Note) : List Note :=
  ns.concatMap fun n =>
    let (n1, n2) := n.splitBeforeY y
    match hmatch : n1, n2 with
    | none, none => []
    | none, some n2 => [n2.moveDownOne]
    | some n1, none => [n1]
    | some n1, some n2 => [n1, n2.moveDownOne]

@[aesop safe apply]
theorem Note.toSpanY_moveDown_disjoint_toSpanY_moveDown_of_disjoint {n m : Note}
    (hnm : Note.disjoint n m) :
    Note.toSpanY (Note.moveDownOne n) |>.disjoint (Note.moveDownOne m).toSpanY := by
  rcases n with ⟨nloc, npitch, n_nsteps, n_hnsteps⟩
  rcases m with ⟨mloc, mpitch, m_nsteps, m_hnsteps⟩
  rcases nloc with ⟨nx, ny⟩
  rcases mloc with ⟨mx, my⟩
  simp_all [Note.toSpanY, Note.moveDownOne, Note.disjoint, SpanY.disjoint,
    Loc.moveDownOne, LocMoveAction.act]; omega

@[note_omega]
def Note.before (n m : Note) : Prop := n.loc.y ≤ m.loc.y

instance : Decidable (Note.before m n) := by
  simp [Note.before]
  infer_instance

instance : DecidableRel Note.before := fun n1 n2 => by infer_instance

instance : IsTotal Note Note.before where
  total n m := by
    simp [Note.before]
    omega

instance : IsTrans Note Note.before where
  trans n m := by
    simp [Note.before]
    omega

def Track.Sorted (t : Track) : Prop :=
  t.notes.Sorted Note.before

/-- If the original list of notes is disjoint, then so is the sorted list. -/
theorem Track.disjont_sorted_of_disjoint {ns : List Note} (hns : ns.Pairwise Note.disjoint)
    : (ns.mergeSort Note.before).Pairwise Note.disjoint := by
  apply List.Pairwise.perm hns
  · rw [List.perm_comm]
    apply List.perm_mergeSort
  · intros n m hnm
    simp_all [SpanY.disjoint_comm]

def Track.sort (t : Track) : { t : Track // t.Sorted } :=
  ⟨{ t with
    notes := t.notes.mergeSort Note.before,
    hdisjoint := Track.disjont_sorted_of_disjoint t.hdisjoint
  }, by
    simp [Track.Sorted]
    apply List.sorted_mergeSort
  ⟩

instance : Preorder Note where
  le := Note.before
  le_refl := by simp [Note.before]
  le_trans := by simp [Note.before]; omega

def notes_get_last_played_y (ns : List Note) (y0 : Nat) : { y0' : Nat // y0' ≥ y0 ∧ (∀ n ∈ ns, y0' ≥ n.loc.y + n.nsteps) } :=
  match ns with
  | [] => ⟨y0, by simp⟩
  | n :: ns' =>
    let ⟨yns, hynsy0, hynsmem⟩ := notes_get_last_played_y ns' y0
    ⟨max (n.loc.y + n.nsteps) yns, by
      simp only [ge_iff_le, le_max_iff, List.mem_cons, forall_eq_or_imp]
      constructor
      · omega
      · constructor
        · omega
        · intros m hm
          specialize (hynsmem m hm)
          omega
    ⟩

/-- Move from top to bottom on a spanY, applying the function to each note,
  with the postcondition that the new notes are at least as far down as the input asks them to be.
-/
def Track.ripplerSorted (ns : List Note)
    (hnsorted : ns.Sorted Note.before)
    (y0 : Nat)
    (hndisjoint : ns.Pairwise Note.disjoint)
    (f : (ycur : Nat) → (n : Note) → { ls : List Note // (∀ {n : Note} (hn : n ∈ ls), n.loc.y ≥ ycur) ∧ ls.Pairwise Note.disjoint}) :
    { ms : List Note // (∀ {m : Note} (hn : m ∈ ms), m.loc.y ≥ y0) ∧ ms.Pairwise Note.disjoint } :=
  match ns with
  | [] => ⟨[], by simp⟩
  | m :: ms =>
    let ⟨outm, houtmge, houtnmdisj⟩ := f y0 m
    let ⟨y0', hy0'y0, hy0'outm⟩ := notes_get_last_played_y outm y0
    have hmsorted : ms.Sorted Note.before := by simp_all
    have hmdisjoint : ms.Pairwise Note.disjoint := by simp_all
    let ⟨outms, houtmsge, houtmsdisj⟩ := Track.ripplerSorted ms hmsorted y0' hmdisjoint f
    ⟨outm ++ outms, by
      rw [List.pairwise_append]
      repeat constructor
      · intros k hk
        simp at hk
        rcases hk with hk | hk
        · specialize (houtmge hk)
          omega
        · specialize (houtmsge hk)
          omega
      · constructor
        · assumption
        · constructor
          · assumption
          · intros k hk l hl
            specialize (houtmge hk)
            specialize (houtmsge hl)
            specialize (hy0'outm k hk)
            simp [Note.toSpanY, SpanY.disjoint]
            right
            sorry
    ⟩



/- Run a worklist algorithm to resolve conflicts.
This allows us to write sound but incomplete algorithms.
This is good for prorotyping new ideas without having to verify new manipulations.
-/
namespace QuadraticSolver

/- The conflict resolution function. -/
variable (resolver : (n m : Note) → (hnm  : ¬ n.toSpanY.disjoint m.toSpanY) →
 { nm : Note × Note // nm.1.disjoint nm.2 })

/-- Check if all notes in 'ns' is disjoint with 'n'. -/
def check_all_disjointAux (n : Note) (ns : List Note) :
    Option { ms : List Note // (∀ m ∈ ms, n.toSpanY.disjoint m.toSpanY) ∧ ms = ns } :=
  match ns with
  | [] => some ⟨[], by aesop⟩
  | m :: ms =>
    if hnm : n.toSpanY.disjoint m.toSpanY
    then
      match hms : check_all_disjointAux n ms with
      | none => none
      | some ⟨ms', hms'⟩ => some ⟨m :: ms', by aesop⟩
    else none

def check_all_disjoint (ns : List Note) : Option { ms : List Note // ns.Pairwise Note.disjoint ∧ ms = ns } :=
  match ns with
  | [] => some ⟨[], by aesop⟩
  | n :: ns' =>
    match check_all_disjointAux n ns' with
    | none => none
    | some ⟨ns'', hns''⟩ =>
      match check_all_disjoint ns' with
      | none => none
      | some ⟨ns''', hns'''⟩ => some ⟨n :: ns''', by aesop⟩

/--
We implement a DPLL style algorithm where we detect conflicts,
and then try to resolve them by reducing a conflict locally, as allowed by fuel.
This solver does not exploit any additional structure, such as the list being sorted,
and therefore requires no preconditions on the function 'f'.
-/
def list_note_resolve_conflict (fuel : Nat) (ns : List Note) :
  Option { ns : List Note // ns.Pairwise (fun n m => n.toSpanY.disjoint m.toSpanY)  } :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match ns with
    | [] => some ⟨[], by aesop⟩
    | n :: [] => some ⟨n :: [], by aesop⟩
    | n :: m :: ns' =>
      let nm' : { nm : Note × Note //  nm.1.disjoint nm.2 } :=
        if hnm : (n.toSpanY.disjoint m.toSpanY)
        then ⟨(n, m), by aesop⟩
        else resolver n m (by aesop)
      let n := nm'.1.1
      let m := nm'.1.2
      match list_note_resolve_conflict fuel (m :: ns')  with
      | none => none
      | some ⟨ms'', hms''⟩ =>
        match check_all_disjointAux n ms'' with
        | none => none
        | some ⟨ms''', hms'''⟩ => some ⟨n :: ms''', by aesop⟩

end QuadraticSolver

section Newline

def Track.splitNoteBeforeY (y : Nat) (n : Note) : List Note :=
    let (n1, n2) := n.splitBeforeY y
    match hmatch : n1, n2 with
    | none, none => []
    | none, some n2 => [n2]
    | some n1, none => [n1]
    | some n1, some n2 => [n1, n2]

@[aesop safe forward]
theorem Track.contains_of_splitNoteBeforeY {y : Nat} {n m : Note}
    (hm : m ∈ Track.splitNoteBeforeY y n) : n.toSpanY.containsSpanY m.toSpanY := by
  simp [Track.splitNoteBeforeY] at hm
  split at hm <;> aesop

@[aesop safe forward]
theorem Track.disjoint_of_splitNoteBeforeY {y : Nat} {n : Note} :
    List.Pairwise Note.disjoint (Track.splitNoteBeforeY y n) := by
  simp [Track.splitNoteBeforeY]
  split <;> aesop
/-- A version that only splits, does no movement nonsense. -/
def Track.splitNotesBeforeY (y : Nat) (ns : List Note) : List Note :=
  ns.concatMap (Track.splitNoteBeforeY y)

@[aesop safe forward]
theorem Track.disjoint_of_splitNotesBeforeY {y : Nat} {ns : List Note}
    {hns : ns.Pairwise Note.disjoint} : (Track.splitNotesBeforeY y ns).Pairwise Note.disjoint := by
  simp [Track.splitNotesBeforeY]
  apply List.pairwise_concatMap_of_pairwise
  · intros a
    aesop
  · intros a b a' b' ha' hb' hab
    simp
    obtain ha' : a.toSpanY.containsSpanY a'.toSpanY := by
      apply Track.contains_of_splitNoteBeforeY ha' -- TODO: aesop?
    obtain hb' : b.toSpanY.containsSpanY b'.toSpanY := by
      apply Track.contains_of_splitNoteBeforeY hb' -- TODO: aesop?
    apply SpanY.disjoint_of_contains_of_contains ha' hb'
    exact hab -- TODO: change argument order to prevent metavar
  · exact hns

/--
If after splitting, the note contains the y position,
then it must contain the entire note.
 -/
theorem Track.containsY_iff_toSpanY_bottom_le_of_mem_splitNoteBeforeY
    (hm : m ∈ Track.splitNoteBeforeY y n) :
    m.toSpanY.containsY y ↔ m.toSpanY.bottom ≤ y := by sorry -- HERE HERE E


def resolverPushDown (n m : Note) (_hnm : ¬ n.toSpanY.disjoint m.toSpanY) :
    { nm : Note × Note // nm.1.disjoint nm.2 } :=
  ⟨(n, { m with loc := ⟨m.loc.x, n.loc.y + n.nsteps⟩}), by simp [SpanY.disjoint, Note.toSpanY]⟩

/-- move all notes with n.y ≥ y to y + 1 -/
def Track.insertNewlineAtAux (ns : List Note) (y : Nat) : Option { ns : List Note // ns.Pairwise Note.disjoint } :=
  let ns := Track.splitNotesBeforeY y ns
  let ns := ns.map (fun n => if n.loc.y < y then n else n.moveDownOne)
  QuadraticSolver.list_note_resolve_conflict resolverPushDown 100 ns


/-- TODO: Still not the right behaviour, since it does not split notes at the cursor. -/
@[export monodrone_ctx_newline]
def RawContext.newlineSolver (ctx : @&RawContext) : RawContext :=
  { ctx with
    track := ctx.track.modifyForgettingFuture
      (fun t =>
        match Track.insertNewlineAtAux t.notes ctx.cursor.cur.cursor.y with
        | none => t
        | some ⟨ns, hns⟩ => { t with notes := ns, hdisjoint := hns }
      )
  }


def Track.resolveWithPushDown  (default : Track) (ns : List Note) (fuel : Nat := ns.length * 2) : Track :=
  match QuadraticSolver.list_note_resolve_conflict resolverPushDown fuel ns with
  | none => default
  | some ⟨ns', hns'⟩ => { default with notes := ns', hdisjoint := hns' }

def Track.resolveWithPushUp  (default : Track) (ns : List Note) : Track :=
  match QuadraticSolver.check_all_disjoint ns with
  | none => default
  | some ⟨ns', hns'⟩ => { default with notes := ns', hdisjoint := by aesop }

def Track.trySetNotes  (default : Track) (ns : List Note) : Track :=
  match QuadraticSolver.check_all_disjoint ns with
  | none => default
  | some ⟨ns', hns'⟩ => { default with notes := ns', hdisjoint := by aesop }

abbrev MAX_WIDTH : Nat := 100 -- TODO: make all width a Fin MAX_WIDTH.

def Span.atYSpanningX (y : Nat) : Span :=
  { topLeft := { x := 0, y := y} , height := 1, width := MAX_WIDTH, hwidth := by simp, hheight := by simp }

@[aesop safe]
theorem Note.contains_of_decreaseSteps (n m : Note) (hm : m ∈ n.decreaseSteps) :
    n.toSpanY.containsSpanY m.toSpanY := by
  simp [Note.decreaseSteps] at hm
  by_cases h : 1 < n.nsteps
  case neg =>
    simp [h] at hm
  case pos =>
    simp [h] at hm
    subst hm
    simp [Note.toSpanY, SpanY.containsSpanY]

@[export monodrone_ctx_delete_note]
def RawContext.deleteNote (ctx : @&RawContext) : RawContext :=
  let cursor := ctx.cursor.cur.cursor
  let ns := ctx.track.cur.notes
  let deleted? := ns.any (fun n => n.toSpanY.containsLoc cursor)
  let ns' := ns.map? (fun n => if n.toSpanY.containsLoc cursor then n.decreaseSteps else n)
  let cursor' := if deleted? then cursor else cursor.moveUpOne
  { ctx with
    track := ctx.track.setForgettingFuture
        { ctx.track.cur with
          notes := ns'
          hdisjoint := by
            simp [ns', ns]
            apply List.Pairwise_map?_of_pairwise (hl := ctx.track.cur.hdisjoint)
            intros n m n' m' hn' hm' hnm
            simp
            sorry -- case analysis

        }
    cursor := ctx.cursor.setForgettingFuture
      ({ ctx.cursor.cur with cursor := cursor' })

  }

@[export monodrone_ctx_delete_line]
def RawContext.deleteLine (ctx : @&RawContext) : RawContext :=
  let cursor := ctx.cursor.cur.cursor
  let ns := ctx.track.cur.notes
  let deleted? := ns.any (fun n => n.toSpanY.containsLoc cursor)
  let ns := ns.map? (fun n => if n.toSpanY.containsLoc cursor then n.decreaseSteps else n)
  let ns :=
    if ¬ deleted?
    then ns.map (fun n => if n.loc.x == cursor.x && n.loc.y > cursor.y then n.moveUpOne else n)
    else ns
  let cursor' := if deleted? then cursor else cursor.moveUpOne
  { ctx with
    track := ctx.track.setForgettingFuture (ctx.track.cur.trySetNotes ns)
    cursor := ctx.cursor.setForgettingFuture
      ({ ctx.cursor.cur with cursor := cursor' })

  }


-- /--This too is subtle, because we need to split the note that crosses the y. -/
-- @[export monodrone_ctx_newline]
set_option trace.aesop true in
def RawContext.newlineVerified (ctx : @&RawContext) : RawContext :=
  { ctx with
    track := ctx.track.modifyForgettingFuture
      (fun t =>
        { t with
          notes := Track.splitBeforeYAux (ctx.cursor.cur.cursor.y) t.notes,
          hdisjoint := by
            simp [Track.splitBeforeYAux]
            apply List.pairwise_concatMap_of_pairwise (hl := t.hdisjoint)
            intros n
            generalize htop : (n.splitBeforeY ctx.cursor.cur.cursor.y).1 = top
            generalize hbot : (n.splitBeforeY ctx.cursor.cur.cursor.y).2 = bot
            · rcases top with rfl | top
              · rcases bot with rfl | bot
                · simp
                · simp [t.hdisjoint]
              · rcases bot with rfl | bot
                · simp [t.hdisjoint]
                · simp
                  apply Note.moveDownOne_disjoint_of_disjoint_of_le
                  · apply Nat.le_of_lt
                    apply Note.y_lt_y_of_splitBeforeY htop hbot
                  · apply Note.disjoint_of_splitBeforeY htop hbot
            · simp
              intros a a' b b'
              generalize hsplita : a.splitBeforeY ctx.cursor.cur.cursor.y = splita
              generalize hsplita' : a'.splitBeforeY ctx.cursor.cur.cursor.y = splita'
              rcases splita with ⟨rfl | topa, rfl | bota⟩ <;>
                rcases splita' with ⟨rfl | topa', rfl | bota'⟩ <;> simp
              · sorry
              · sorry
              · sorry
              · sorry
              · sorry
              · sorry
              · sorry
              · sorry
              · sorry


        })
  }

end Newline


section DragDown

@[export monodrone_ctx_drag_down_one]
def RawContext.dragDownOne (ctx : @&RawContext) : RawContext :=
  let cursor := ctx.cursor.cur.cursor
  let cursor' := cursor.moveDownOne
  if cursor = cursor'
  then ctx
  else
    { ctx with
      track := ctx.track.modifyForgettingFuture
        (fun t =>
          let ns := t.notes
          let ns := ns.map (fun n =>
            if n.toSpanY.containsLoc cursor
            then
              if n.loc == cursor
              then
                if hnsteps1 : n.nsteps = 1
                then n.increaseNSteps
                else n.decreaseSteps' (by have h₁ := n.hnsteps; omega) |>.moveDownOne
              else n.increaseNSteps
            else n)
          let t := t.trySetNotes ns
          t
        )
      cursor := ctx.cursor.modifyForgettingFuture (fun s => { s with cursor := cursor' })
    }

end DragDown

section DragUp

@[export monodrone_ctx_drag_up_one]
def RawContext.dragUpOne (ctx : @&RawContext) : RawContext :=
  let cursor := ctx.cursor.cur.cursor
  let cursor' := cursor.moveUpOne
  if cursor = cursor'
  then ctx
  else
    { ctx with
      track := ctx.track.modifyForgettingFuture
        (fun t =>
          let ns := t.notes
          let ns := ns.map (fun n =>
            if n.toSpanY.containsLoc n.loc
            then
              if cursor == n.loc
              then n.moveUpOne.increaseNSteps
              else
                n -- TODO: fix !
                -- if hn : n.hnsteps > 1
                -- then n.decreaseSteps' (by have h₁ := n.hnsteps; omega) |>.moveUpOne
                -- else n.increaseNSteps
            else n)
          let t := t.trySetNotes ns
          t
        )
      cursor := ctx.cursor.modifyForgettingFuture (fun s => { s with cursor := cursor' })

    }

end DragUp

def Loc.aboveLocWithSameX (l1 l2 : Loc) : Prop := l1.y < l2.y && l1.x = l2.x

instance : Decidable (Loc.aboveLocWithSameX l1 l2) := by
  simp [Loc.aboveLocWithSameX]
  infer_instance

def Loc.belowLocWithSameX (l1 l2 : Loc) : Prop := l1.y > l2.y && l1.x = l2.x

instance : Decidable (Loc.belowLocWithSameX l1 l2) := by
  simp [Loc.belowLocWithSameX]
  infer_instance

def Note.setNSteps? (n : Note) (nsteps : Nat) : Option Note :=
  if hnsteps : nsteps = 0
  then none
  else some { n with nsteps := nsteps, hnsteps := by omega }

def Note.moveDown' (n : Note) (delta : Int) : Note :=
  { n with loc := { n.loc with y := ((Int.ofNat n.loc.y)  + delta).toNat } }

def Track.setNSteps (t : Track) (cursor : Loc) (nsteps : Nat) : Track :=
  let n? := t.notes.find? (fun n => n.toSpanY.containsLoc cursor)
  { t with
    notes := t.notes.map? (fun n =>
      if n.toSpanY.containsLoc cursor
      then n.setNSteps? nsteps
      else
        match n? with
        | .none => n
        | .some n' =>
            if n.toSpanY.topLeft.belowLocWithSameX cursor
            then n.moveDown' (((Int.ofNat nsteps) - (Int.ofNat n'.nsteps)) : Int)
            else n)
    hdisjoint := sorry
  }

@[export monodrone_ctx_set_nsteps]
def RawContext.setNSteps (ctx : @&RawContext) (nsteps : UInt64) : RawContext :=
  let cursor := ctx.cursor.cur.cursor
  { ctx with
    track := ctx.track.modifyForgettingFuture fun t => t.setNSteps cursor nsteps.toNat
  }

def Track.increaseNSteps (t : Track) (l : Loc) : Track :=
  let n? : Option Note := t.notes.find? (fun n => n.toSpanY.containsLoc l)
  match n? with
  | none => t
  | some n =>
    t.setNSteps l (n.nsteps + 1)

@[export monodrone_ctx_increase_nsteps]
def RawContext.increaseNSteps (ctx : @&RawContext) : RawContext :=
  let cursor := ctx.cursor.cur.cursor
  { ctx with
    track := ctx.track.modifyForgettingFuture fun t => t.increaseNSteps cursor
  }

def Track.decreaseNSteps (t : Track) (l : Loc) : Track :=
  let n? : Option Note := t.notes.find? (fun n => n.toSpanY.containsLoc l)
  match n? with
  | none => t
  | some n =>
    t.setNSteps l (n.nsteps - 1)

@[export monodrone_ctx_decrease_nsteps]
def RawContext.decreaseNSteps (ctx : @&RawContext) : RawContext :=
  let cursor := ctx.cursor.cur.cursor
  { ctx with
    track := ctx.track.modifyForgettingFuture fun t => t.decreaseNSteps cursor
  }


@[export monodrone_ctx_set_pitch]
def RawContext.setPitchName (ctx : @&RawContext) (p : UInt64) : RawContext :=
  { ctx with track :=
    ctx.track.modifyForgettingFuture fun t =>
      t.addNoteAtLoc (PitchName.ofUInt64 p) ctx.cursor.cur.topLeft
  }

@[note_omega]
def Span.containsY (s : Span) (y : Nat) : Prop :=
  s.topLeft.y ≤ y ∧ y < s.topLeft.y + s.height

instance : Decidable (Span.containsY s y) := by
  simp [Span.containsY]
  infer_instance


@[export monodrone_ctx_decrease_duration]
def RawContext.decreaseDuration (ctx : @&RawContext) : RawContext :=
  { ctx with track :=
    ctx.track.modifyForgettingFuture fun t =>
      t.decreaseDuration ctx.cursor.cur.toSpan
  }

@[export monodrone_ctx_toggle_sharp]
def RawContext.toggleSharp (ctx : @&RawContext) : RawContext :=
  { ctx with track :=
    ctx.track.modifyForgettingFuture fun t =>
      t.toggleAccidental Accidental.sharp ctx.cursor.cur.toSpan
  }

@[export monodrone_ctx_toggle_flat]
def RawContext.toggleFlat (ctx : @&RawContext) : RawContext :=
  { ctx with track :=
    ctx.track.modifyForgettingFuture fun t =>
      t.toggleAccidental Accidental.flat ctx.cursor.cur.toSpan
  }

@[export monodrone_ctx_lower_octave]
def RawContext.lowerOctave (ctx : @&RawContext) : RawContext :=
  { ctx with
    track :=
      ctx.track.modifyForgettingFuture fun t => t.modifyOverlapSpan ctx.cursor.cur.toSpan
          (f := fun n => .some { n with userPitch := n.userPitch.lowerOctave })
          (hf := by
            intros n n' s hs hn'
            rcases n with ⟨nloc, npitch, nsteps, hnsteps⟩
            simp only [Option.mem_def, Option.some.injEq] at hn'
            rw [← hn', Note.toSpanY]
            apply SpanY.containsSpanY_refl)
  }

@[export monodrone_ctx_raise_octave]
def RawContext.raiseOctave (ctx : @&RawContext) : RawContext :=
  { ctx with
    track :=
      ctx.track.modifyForgettingFuture fun t => t.modifyOverlapSpan ctx.cursor.cur.toSpan
          (f := fun n => .some { n with userPitch := n.userPitch.raiseOctave })
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

@[export monodrone_note_get_octave]
def noteGetOctave (n : @&Note) : UInt64 :=
  n.userPitch.octave.toUInt64

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

@[export monodrone_note_get_accidental]
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

@[export monodrone_ctx_to_json_str]
def RawContext.toJsonStr (ctx : @&RawContext) : String :=
  s!"{ToJson.toJson ctx}"

@[export monodrone_ctx_from_json_str]
def RawContext.fromJson (s : String) : IO RawContext :=
  match Json.parse s >>= fromJson?  with
  | Except.ok ctx => return ctx
  | Except.error e => throw <| IO.userError s!"parse error: '{e}'. Raw JSON file: '{s}'"

/-# Metadata getters and setters -/

@[export monodrone_ctx_get_track_name]
def RawContext.getTrackName (ctx : @&RawContext) : String := ctx.track_name

@[export monodrone_ctx_get_artist_name]
def RawContext.getArtistName (ctx : @&RawContext) : String := ctx.artist_name

@[export monodrone_ctx_get_time_signature_fst]
def RawContext.getTimeSignatureFst (ctx : @&RawContext) : UInt64 := ctx.time_signature.fst.toUInt64

@[export monodrone_ctx_get_time_signature_snd]
def RawContext.getTimeSignatureSnd (ctx : @&RawContext) : UInt64 := ctx.time_signature.snd.toUInt64

@[export monodrone_ctx_set_track_name]
def RawContext.setTrackName (ctx : @&RawContext) (str : String) : RawContext :=
  { ctx with track_name := str }

@[export monodrone_ctx_set_artist_name]
def RawContext.setArtistName (ctx : @&RawContext) (str : String) : RawContext :=
  { ctx with artist_name := str }

@[export monodrone_ctx_set_time_signature]
def RawContext.setTimeSignature (ctx : @&RawContext) (fst snd : UInt64) : RawContext :=
  { ctx with time_signature := (fst.toNat, snd.toNat) }

end ffi
