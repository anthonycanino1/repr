Require Import Coq.omega.Omega.
Ltac omega := Coq.omega.Omega.omega.


(* Some convience tactics. Nothing special *)
Ltac extend pf :=
  let H := type of pf in
  match goal with
    | [ _ : H |- _ ] => fail 
    | _ => 
      let H := fresh "Hextend" in
      generalize pf; intros H
  end.

(********************************************************************)
(* introh tactic : Simple wrapper around intros that automatically 
 * pulls quantifier variables so we can focus on naming hypotheses *)
Ltac introh_rec :=
  match goal with
    | [ |- ?P -> ?Q ]    => idtac 
    | [ |- forall _, _ ] => intro; introh_rec
    | [ |- _ ]           => idtac
  end.

Ltac introh_arg name :=
  introh_rec ;
  match goal with
    | [ |- ?P -> ?Q ] => intro name
  end.

Tactic Notation "introh" simple_intropattern(I1) :=
  introh_arg I1.

Tactic Notation "introh" simple_intropattern(I1) simple_intropattern(I2) :=
  introh I1 ; introh I2.

Tactic Notation "introh" simple_intropattern(I1) simple_intropattern(I2) 
  simple_intropattern(I3) :=
   introh I1 ; introh I2 I3.

Tactic Notation "introh" simple_intropattern(I1) simple_intropattern(I2) 
 simple_intropattern(I3) simple_intropattern(I4) :=
  introh I1 ; introh I2 I3 I4.

Tactic Notation "introh" simple_intropattern(I1) simple_intropattern(I2) 
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern (I5) :=
  introh I1 ; introh I2 I3 I4 I5.

  

(* Taken from Software Foundations *)
Tactic Notation "solve_by_inversion_step" tactic(t) :=  
  match goal with  
    | H : _ |- _ => solve [ inversion H; subst; t ] 
  end
  || fail "because the goal is not solvable by inversion.".

Tactic Notation "solve" "by" "inversion" "1" :=
  solve_by_inversion_step idtac.
Tactic Notation "solve" "by" "inversion" "2" :=
  solve_by_inversion_step (solve by inversion 1).
Tactic Notation "solve" "by" "inversion" "3" :=
  solve_by_inversion_step (solve by inversion 2).
Tactic Notation "solve" "by" "inversion" :=
  solve by inversion 1.


(* Tactics defined for readability *)
Tactic Notation "clean" "1" := try solve by inversion 1.
Tactic Notation "clean" "2" := try solve by inversion 2.
Tactic Notation "clean" "3" := try solve by inversion 3.


(* Specialize as far as possible *)

Ltac spec :=
  try (
    match goal with
      | [H1: ?A -> ?B, H2: ?A |- _ ] => specialize (H1 H2); spec
    end
  ).





