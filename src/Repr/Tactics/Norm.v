Require Import Repr.Tactics.LibTactics.
Require Import Repr.Tactics.All.
Require Import Repr.Tactics.Rewrite.
Require Import Repr.Tactics.Burn.

Require Import Coq.Arith.Peano_dec.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.Lt.

(********************************************************************)
Lemma S_min_n
  :  forall (n:nat)
  ,  n > 0
  -> S (n - 1) = n.
Proof. rip; burn. Qed.
Hint Rewrite S_min_n.

(********************************************************************)

Ltac norm_nat_compare :=
  match goal with
    (* Eq *)
    | [ H : nat_compare _ _ = Eq |- _ ] 
      => apply nat_compare_eq in H 

    | [ H : Eq = nat_compare _ _ |- _ ] 
      => symmetry in H; apply nat_compare_eq in H 

    | [ H : context [ nat_compare _ _ = Eq ] |- _ ]
      => rewrite <- nat_compare_eq in H

    | [ H : context [ Eq = nat_compare _ _ ] |- _ ]
      => symmetry in H; rewrite <- nat_compare_eq in H

    (* Lt *)                                                       
    | [ H : nat_compare _ _ = Lt |- _ ] 
      => apply nat_compare_lt in H 

    | [ H : Lt = nat_compare _ _ |- _ ] 
      => symmetry in H; apply nat_compare_lt in H 

    | [ H : context [ nat_compare _ _ = Lt ] |- _ ]
      => rewrite <- nat_compare_lt in H

    | [ H : context [ Lt = nat_compare _ _ ] |- _ ]
      => symmetry in H; rewrite <- nat_compare_lt in H

    (* Gt *)                                                       
    | [ H : nat_compare _ _ = Gt |- _ ] 
      => apply nat_compare_gt in H 

    | [ H : Gt = nat_compare _ _ |- _ ] 
      => symmetry in H; apply nat_compare_gt in H 

    | [ H : context [ nat_compare _ _ = Gt ] |- _ ]
      => rewrite <- nat_compare_gt in H

    | [ H : context [ Gt = nat_compare _ _ ] |- _ ]
      => symmetry in H; rewrite <- nat_compare_gt in H
  end.
   
Ltac break_nat_compare :=
  match goal with 
    | [ |- context [ nat_compare ?E1 ?E2 ] ]
      => let X := fresh "X" in
         remember (nat_compare E1 E2) as X; 
         destruct X;
         norm_nat_compare;
         subst
  end.
