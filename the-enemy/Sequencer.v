From Coq Require Import List Lia PeanoNat.
Import ListNotations.

(*** Trivial lemmas ***)

Lemma singExt α (a a': α): a = a' -> [a] = [a'].
Proof. now intros; subst. Qed.

Lemma consExt α (a a': α) (l l': list α): a = a' -> l = l' -> a :: l = a' :: l'.
Proof. now intros; subst. Qed.

(*** Actual theory ***)

Definition pitch := nat.
Record note := {
  nPitch: pitch;
  nStart: nat;
  nLenM1: nat;
}.
Definition nLen n := S (nLenM1 n).
Definition nEnd n := nStart n + nLen n.
Definition track := list note.

Ltac Zify.zify_pre_hook ::=
  unfold nLen, nEnd in *; cbn.

Inductive startsBeforeTrack: nat -> track -> Prop :=
  | sbtNil pos: startsBeforeTrack pos []
  | sbtOne pos n t (Hbefore: pos <= nStart n): startsBeforeTrack pos (n :: t).

Definition noteExt (p p': pitch) (s s': nat) (l l': nat):
  p = p' -> s = s' -> l = l' -> Build_note p s l = Build_note p' s' l'.
Proof. now repeat intros ->. Qed.

Inductive wf: track -> Prop :=
  | wf_nil: wf []
  | wf_one n: wf [n]
  | wf_seq (n1 n2: note) (t: track) (Horder: nEnd n1 <= nStart n2)
           (IH: wf (n2 :: t)): wf (n1 :: n2 :: t).

Inductive cell: Type :=
  | cPitch (p: pitch)
  | cCont
  | cEmpty.
Definition matrix := list cell.

Inductive notCont: matrix -> Prop :=
  | ncNil: notCont []
  | ncPitch p m: notCont (cPitch p :: m)
  | ncEmpty m: notCont (cEmpty :: m).

Definition linearizeNote (n: note): matrix :=
  cPitch (nPitch n) :: repeat cCont (nLenM1 n).
Arguments linearizeNote: simpl never.

Fixpoint linearizeTrack (t: track) (pos: nat): matrix :=
  match t with
  | [] => []
  | n :: t' => repeat cEmpty (nStart n - pos)
               ++ linearizeNote n
               ++ linearizeTrack t' (nEnd n)
  end.

Lemma notCont_cEmpty a m: notCont m -> notCont (repeat cEmpty a ++ m).
Proof. destruct a; [auto|constructor]. Qed.

Lemma notCont_linearizeTrack (t: track) pos: notCont (linearizeTrack t pos).
Proof. destruct t; try apply notCont_cEmpty; constructor. Qed.

Fixpoint parseMatrix (m: matrix) (pos: nat): track :=
  match m with
  | [] => []
  | cEmpty :: m' => parseMatrix m' (S pos)
  | cCont :: m' => parseMatrix m' (S pos) (* unused *)
  | cPitch p :: m' => parseCont m' (S pos) p 0
  end
with parseCont (m: matrix) (pos: nat) (p: pitch) (lenM1: nat): track :=
  let note := {| nPitch := p; nStart := pos - S lenM1; nLenM1 := lenM1 |} in
  match m with
  | [] => [note]
  | cEmpty :: m' => note :: parseMatrix m' (S pos)
  | cCont :: m' => parseCont m' (S pos) p (S lenM1)
  | cPitch p :: m' => note :: parseCont m' (S pos) p 0
  end.

Lemma parseMatrix_cCont (a b c: nat) (p: pitch) (m: matrix):
  notCont m ->
  parseCont (repeat cCont a ++ m) b p c =
    {| nPitch := p; nStart := b - S c; nLenM1 := a + c |} :: parseMatrix m (a + b).
Proof.
  revert b c. induction a; intros; cbn.
  - now inversion_clear H.
  - rewrite (IHa (S b) (S c)); auto.
    apply consExt. apply noteExt; lia. f_equal; lia.
Qed.

Lemma parseMatrix_linearizeNote (n: note) (m: matrix) (Hnc: notCont m):
  parseMatrix (linearizeNote n ++ m) (nStart n) = n :: parseMatrix m (nEnd n).
Proof.
  destruct n as [p start len]; unfold linearizeNote; cbn.
  rewrite parseMatrix_cCont; auto.
  apply consExt. apply noteExt; lia. f_equal; lia.
Qed.

Lemma parseMatrix_cEmpty (m: matrix) (a b: nat):
  parseMatrix (repeat cEmpty a ++ m) b = parseMatrix m (a + b).
Proof.
  revert b; induction a; [easy|cbn; intros].
  rewrite IHa. f_equal; lia.
Qed.

Proposition parseMatrix_linearizeTrack (t: track) (Hwf: wf t) (pos: nat):
  startsBeforeTrack pos t -> parseMatrix (linearizeTrack t pos) pos = t.
Proof.
  induction t as [|n t]; [easy|intros Hsbt].
  destruct t as [|t']; inversion_clear Hwf; inversion_clear Hsbt; cbn.
  - rewrite parseMatrix_cEmpty, Nat.sub_add; [|lia].
    apply parseMatrix_linearizeNote; constructor.
  - rewrite parseMatrix_cEmpty, Nat.sub_add; [|lia].
    rewrite <- (IHt IH); [|constructor; lia].
    rewrite parseMatrix_linearizeNote; auto; cbn.
    * rewrite !parseMatrix_cEmpty. do 2 f_equal; lia.
    * apply notCont_cEmpty; constructor.
Qed.
