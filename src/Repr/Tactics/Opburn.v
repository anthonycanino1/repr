Require Import Omega.
Require Import List.

Require Import Repr.Tactics.Plugin.ConstructionTac.

(* Searches for x in a left-associated list of nested tuples *)
Ltac in_list ls x :=
  match ls with
    | x => idtac
    | (_, x) => idtac
    | (?ls', _) => in_list ls' x
  end.

(** Try calling tactic function [f] on all hypotheses, keeping the first application that doesn't fail. *)
Ltac app_hyps f :=
  match goal with
    | [ H : _ |- _ ] => f H
  end.

(** Try calling tactic function [f] on every element of tupled list [ls], keeping the first call not to fail. *)
Ltac app ls f :=
  match ls with
    | (?LS, ?X) => f X || app LS f || fail 1
    | _ => f ls
  end.

(** Run [f] on every element of [ls], not just the first that doesn't fail. *)
Ltac all ls f :=
  match ls with
    | (?LS, ?X) => f X; all LS f
    | (_, _) => fail 1
    | _ => f ls
  end.

(* Tactic to get rid of the manual rip/intros gen cycle *)
Ltac loosen t :=
  let rec gen_ls ls :=
    match ls with
      | false        => idtac
      | (t,   ?ls')  => gen_ls ls'
      | (?t', ?ls')  => generalize dependent t' ; gen_ls ls'
    end
  in

  let rec loosen_ls ls :=
    match goal with
      | [ |- forall x, _ ] => 
        intro x ;
        loosen_ls (x,ls) 
      | _ => gen_ls ls 
    end
  in
  loosen_ls false.

(* LAST : There is a tradeoff here: We want to perform as many obvious inversions
   as possible. Easy cases where we are confident we are making the right choice.
   (1) Inversion succeeds imediately (clears current goal)
   (2) Inversion introduces a single constructor (simplies current goal)
   (3) Inversion introduces multiple constructors, but they are immediately solved 
       with eauto. *)
Ltac simpl_hyp inv_one := 
  (* From Chlipala: Helper tactic that inverts a hypothesis with a predicate appearing
     in inv_one iff we immediately clear the inversion or it leaves 1 constructor *)
  let invert_hyp F H :=
    in_list inv_one F; 

    (* Go with an attempt at quick inversion heuristics first *)
    (inversion H; fail) || 
    (inversion H; [idtac]; clear H; subst) ||

    (* Allow an inversion if all goals are immediately solved with eauto *)
    (inversion H; subst; solve [eauto]; clear H) ||

    (* Allow an inversion if only one goal remains after euato *)
    (inversion H; subst; eauto; [idtac]; clear H) 
  in

  match goal with
    (* Eliminate existential hypothesis *)
    | [ H : ex _ |- _ ] => destruct H

    (* Look for any predicates that can be inverted up to a fixed arity *)
    | [ H : ?F _ |- _ ] => invert_hyp F H
    | [ H : ?F _ _ |- _ ] => invert_hyp F H
    | [ H : ?F _ _ _|- _ ] => invert_hyp F H
    | [ H : ?F _ _ _ _ |- _ ] => invert_hyp F H
    | [ H : ?F _ _ _ _ _ |- _ ] => invert_hyp F H

    (* One more trick for proof search: If we see something that intuition can
       solve, let simpl_hyp pass *)
    | [ H : _ \/ _ |- _ ] => idtac
    | [ H : _ /\ _ |- _ ] => idtac
  end.

Definition done (T : Type) (x : T) := True.
Arguments done [T] _.

Definition gend (T : Type) (x : T) := True.
Arguments gend [T] _.


(* [e] is a universally quantified hypothesis we attemp to instantiate
   [trace] marks the current state of our instantiation. Combine this with
   [done] above to add state to the context. *)
Ltac inster_prim e trace :=
  match type of e with
    | forall x : ?T, _ =>
      (* One modication to the search: We generate all easy constructors for a type
         if we haven't generated them for said type before *)
      (match type of T with
        | Prop => idtac
        | _    => 
          match goal with
            | [ H : gend T |- _ ] => idtac
            | _ => 
              gen_constructors T ; 
              assert (gend T) by constructor
          end
      end) ;

      (* This picks the first context variable with the right type *)
      match goal with
        | [ H : _ |- _ ] =>
          inster_prim (e H) (trace, H)
        | _ => fail 2 
      end
    | _ =>
      (* No more quantifiers, so we check the trace *)
      match trace with
        (_,_) =>
        (* Case is only reached if trace is non-empty, forcing a fail if no 
           progress is made *)
        match goal with 
          | [ H : done (trace, _) |- _ ] =>
            (* Record of the trace in the context, backtrack *)
            fail 1
          | _ =>
            let T := type of e in
            match type of T with
              | Prop =>
                (* [e] is now a proof. Add it to the context and mark the trace *)
                generalize e; intro; assert (done (trace, tt)) by constructor 
              | _ =>
                (* [e] is not a proof. Make sure we have not encountered this case in 
                   the trace before proceeding. *)
                all trace ltac:(fun X =>
                    match goal with
                      | [ H : done (_, X) |- _ ] => fail 1
                      | _ => idtac
                    end);
                let i := fresh "i" in
                pose (i := e); assert (done (trace, i)) by constructor
            end
        end
      end
  end.

(* A Wrapper aroudn inster_prim: Before doing anything, we generate 'easy` constructors
   of the quantified type and add them to the context *)
(* with inster_gen e trace :=
  match type of e with
    | forall x : ?T, _ =>
      (* We need to catch the implication degenerative case of product type
         and cut off the constructor gen *)
      match type of T with
        | Prop => fail 1
        | _    => gen_constructors T ; inster_prim e trace
      end
    | _ =>
      inster_prim e trace
  end. *)

Ltac inster e trace :=
  inster_prim e trace.
  

Ltac un_done :=
  repeat match goal with
           | [ H : done _ |- _ ] => clear H
         end.

Ltac un_gend :=
  repeat match goal with
           | [ H : gend _ |- _ ] => clear H
         end.


Ltac opburn'' lemmas inv_one guide :=
  (* From Chlipala: Combine intuition with some simplification *)
  let sintuition := simpl in *; intuition eauto; subst; 
    repeat (simpl_hyp inv_one; intuition eauto; subst); try congruence in

  (sintuition;
   match lemmas with 
     | tt => idtac
     | _ =>
       repeat (
          try (app_hyps guide) ;
          (app lemmas ltac:(fun L => inster L L) 
           || app_hyps ltac:(fun L => inster L L)) ; 
          repeat (simpl_hyp inv_one; intuition)
         ) ; un_done; un_gend
    end;
    sintuition;
    try omega; try (elimtype False; omega)).

Ltac opburn := opburn'' tt tt ltac:(fun T => idtac).
Ltac opburn' lemmas inv_one := opburn'' lemmas inv_one ltac:(fun T => idtac).

(* Take a guess at specializing a quantified hypothesis H with v,
   but only succeed if we can simplfy the hypothesis after specializing *)
Ltac guess v H :=
  let contains H :=
    match goal with 
      | [ _ : H |- _ ] => idtac
      | _ => fail
    end
  in

  specialize (H v);
  match (type of H) with
    | ?Head -> _ => contains Head
    | _ => fail
  end.
