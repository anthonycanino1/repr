Require Import List.

Require Import Repr.Tactics.All.


(********************************************************************)
(* Definitions *)

Fixpoint get (X:Type) (ls:list X) (idx:nat) : option X :=
  match ls, idx with
    | l :: ls', O      => Some l
    | l :: ls', S idx' => get _ ls' idx'
    | _, _             => None
  end.

Arguments get [X] _ _.

Fixpoint delete (X:Type) (ls:list X) (idx:nat) : list X :=
  match ls, idx with
    | l :: ls', O      => ls'
    | l :: ls', S idx' => l :: delete _ ls' idx'
    | nil, _           => nil
  end.

Arguments delete [X] ls idx.


(********************************************************************)
(* Lemmas *)

Lemma option_inj : 
  forall (x y:Type), 
    x = y -> Some x = Some y.
Proof.
  introh Heq; subst; trivial.
Qed.

Lemma S_lt_length :
  forall X n (x:X) (ls:list X), 
    n < length ls -> S n < length (x :: ls).
Proof.
  induction n; introh Hlt; clean 1; simpl; auto with arith.
Qed.  

Lemma length_lt_S :
 forall X n (x:X) (ls:list X), 
   S n < length (x :: ls) -> n < length ls.
Proof.
  auto with arith.
Qed.

Theorem idx_lt_length : 
  forall X idx (ls:list X), 
    idx < length ls -> exists x, get ls idx = Some x.
Proof.
  induction idx; introh Hlt; destruct ls; simpl; clean 1.
  eexists; trivial.
  apply length_lt_S in Hlt; specialize (IHidx _ Hlt); elim IHidx; intros; rewrite H;
   eexists; reflexivity.
Qed.  

Theorem delete_rewind :
  forall X (idx:nat) (ls:list X) (x:X),
    x :: delete ls idx = delete (x :: ls) (S idx).
Proof.
  intros; simpl; auto.
Qed.
