Require Import Repr.Tactics.LibTactics.
Require Import Repr.Tactics.All.
Require Import Repr.Tactics.Rewrite.


(********************************************************************)
(* Rip Tactic 
 *  - Simplifies the current goal (including hypotheses). 
 *)
Ltac rip :=
  try
    (repeat
       (match goal with
          | [ |- forall _, _  ]              => intros; rip
          | [ H : _ /\ _ |- _ ]              => inverts H; rip
          | [ H1 : ?A -> ?B, H2 : ?A |- _ ]  => specialize (H1 H2); rip
        end
       )
    ).
  
(********************************************************************)
(* Break Tactic 
 *  - Remembers a term and destructs it
 *)
Ltac break_as term id :=
  let name := fresh "bk" in
  remember term as name ;
  match goal with
    | [ H : name = _ |- _ ] => 
      rename H into id ;
      destruct name
  end.

Tactic Notation "break" constr(term) :=
  let I1 := fresh "Heq" in
  break_as term I1.

Tactic Notation "break" constr(term) "as" simple_intropattern(I1) :=
  break_as term I1.
  
  


(********************************************************************)
(* Burn Mega Tactic for semantic proofs
 * - This is my attempt / practice at writing more automated proof,
 *   taken from Iron Lambda. 
 *)

(* First we encode a primitive solver that either succeeds or fails
 * quickly; a common tactic when writing decision procedures *)
Ltac burn0 :=
  first 
    [ assumption    
    | reflexivity   
    | solve [eauto] 
    | omega         
    | false; omega 
    ].

(* This uses the firstorder solver, applying burn0 when no firstorder
 * cannot solve the goal *)       
Ltac burn1 :=
  first
    [ burn0
    | solve [firstorder burn0]
    ].

(* Slight refactoring of the goal before attempting a solve *)
Ltac burn2 :=
  first
    [ burn1
    | f_equal; burn1 
    ].

(* Do the bulk of rewriting work; rewrites are done in various combinations *)
Ltac burn3 :=
  first [ burn2
        | try autorewrite with core in *;
          first [ burn2
                | try rewrite_goal;
                  first [ burn2
                        | simpl;
                          burn2 ] ] ].

Ltac burn4 := 
  rip;
  match goal with 
    [ H1 : _ = ?C ?y1, H2 : _ = ?C ?y2 |- _ ] => 
       assert (y1 = y2); rewrite H1 in H2; inverts H2; burn3

    | [ H1 : ?C ?y1 = _, H2 : ?C ?y2 = _ |- _ ] => 
       assert (y1 = y2); rewrite H1 in H2; inverts H2; burn3

    | _ => burn3
 end.

(* Top level mega-tactic *)
Ltac burn :=
  first [burn0 | burn4].

Ltac tburn :=
  try (first [burn0 | burn4]).