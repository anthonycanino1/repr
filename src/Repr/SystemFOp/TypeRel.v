Require Import List.

Require Import Repr.Lists.

Require Import Repr.Tactics.All.
Require Import Repr.Tactics.Rewrite.
Require Import Repr.Tactics.Burn.
Require Import Repr.Tactics.Norm.
Require Import Repr.Tactics.LibTactics.

Require Import Coq.Arith.Peano_dec.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.Lt.

Require Import Repr.SystemFOp.Kind.
Require Import Repr.SystemFOp.Type.
Require Import Repr.SystemFOp.Term.

Require Import Repr.Tactics.CpdtTactics.
Require Import Repr.Tactics.Opburn.

(* We define the typing relation over kind and type environments. D and G standing
   for delta and gamma resp. *)
Reserved Notation "D '\,' G '||-' t '\:' T" (at level 40).

Inductive type_rel : kenv -> tenv -> term -> typ -> Prop :=
  | TR_NConst :
      forall D G n,
        D \, G ||- (NConst n) \: TNat
  | TR_Add :
      forall D G t1 t2,
        D \, G ||- t1 \: TNat ->
        D \, G ||- t2 \: TNat ->
        D \, G ||- (Add t1 t2) \: TNat
  | TR_Var :
      forall D G x T,
        get G x = Some T ->
        D \\- T \: KStar ->
        D \, G ||- (Var x) \: T 
  | TR_Abs :
      forall D G t T1 T2,
        D \\- T1 \: KStar ->
        D \, (T1 :: G) ||- t \: T2 ->
        D \, G ||- Abs T1 t \: TArrow T1 T2
  | TR_App :
      forall D G t1 t2 T1 T2,
        D \, G ||- t1 \: TArrow T1 T2 ->
        D \, G ||- t2 \: T1 ->
        D \, G ||- App t1 t2 \: T2
  | TR_TyAbs :
      forall D G t T,
        (KStar :: D) \, (tenv_lift 0 G) ||- t \: T ->
        D \, G ||- (TyAbs t) \: TAll T
  | TR_TyApp :
      forall D G t T T', 
        D \, G ||- t \: TAll T ->
        D \\- T' \: KStar ->
        D \, G ||- (TyApp t T') \: [0 |=> T'] T

where "D '\,' G '||-' t '\:' T" := (type_rel D G t T).

Hint Constructors type_rel.

(********************************************************************)
(* On to the substitution lemmas. They have more in common with the
 * typing relation than the proof of soundness, hence, hey remain here. *)

(* Simple tactic that helps burn down the easy cases. *)
Ltac inverts_term :=
  repeat
    (match goal with
       | [ H: _\,_ ||- (NConst _)   \: _ |- _ ] => inverts H
       | [ H: _\,_ ||- (Add _ _)    \: _ |- _ ] => inverts H
       | [ H: _\,_ ||- (Var _)      \: _ |- _ ] => inverts H
       | [ H: _\,_ ||- (Abs _ _)    \: _ |- _ ] => inverts H
       | [ H: _\,_ ||- (App _ _)    \: _ |- _ ] => inverts H
       | [ H: _\,_ ||- (TyAbs _)    \: _ |- _ ] => inverts H
       | [ H: _\,_ ||- (TyApp _ _)  \: _ |- _ ] => inverts H
     end).

(* This tactic 'usually' gets most of the inductive and easy cases
 * when we induct over the typing relation. *)
Tactic Notation "induction_type" ident(t) :=
  induction t; rip; simpl; inverts_term; tburn.

Lemma type_rel_imp_wellformed_term
  :  forall (D:kenv)(G:tenv)(t:term)(T:typ)
  ,  D \, G ||- t \: T
  -> well_formed_term D G t.
Proof.
  loosen t; induction t; opburn' tt type_rel.  
Qed.
Hint Resolve type_rel_imp_wellformed_term.

(* Lemma used to prove kenv_weaking (since its induction hypothesis is not
   strong enough.

   We may insert a kind into a position in the kind environment provided
   we lift over the type environment, term, and type. *)
Lemma kenv_insert
  :  forall (D:kenv)(G:tenv)(t:term)(T:typ)(X:tvar)
  ,  D \, G ||- t \: T
  -> (insert D X KStar) \, (tenv_lift X G) ||- (typ_term_lift X t) \: (typ_lift X T).
Proof.
  rip; gen D G T X; induction_type t.
 
  (* Add *)
  assert (TNat = typ_lift X TNat).
    burn.
  econstructor; burn.

  (* Abs *)
  econstructor. burn. burn.

  (* TyAbs *)
  econstructor. fold typ_lift. rewrite insert_rewind. rewrite tenv_lift_SX.
  burn.

  (* TyApp *)
  break (nat_compare X 0); norm_nat_compare.
  
    (* Case X = 0 *)
    subst.
    assert (0 = 0+0). burn. rewrite H at 5.
    rewrite typ_lift_over_subs'. simpl. 
    econstructor; burn.

    (* Case X < 0 *)
    burn.

    (* Case X > 0 *)
    assert (X = 0+X). burn. rewrite H at 5.
    rewrite typ_lift_over_subs'. simpl.
    econstructor; burn.
Qed.  

Lemma kenv_weakening
  :  forall (D:kenv)(G:tenv)(t:term)(T:typ)(X:tvar)
  ,  D \, G ||- t \: T
  -> (KStar :: D) \, (tenv_lift 0 G) ||- (typ_term_lift 0 t) \: (typ_lift 0 T).
Proof.
  rip; rewrite cons_as_insert; apply kenv_insert; burn.
Qed.
Hint Resolve kenv_weakening.

Lemma tenv_weakening
  :  forall (D:kenv)(G:tenv)(t:term)(T:typ)(x:var)
  ,  D \, delete G x ||- t \: T
  -> D \, G ||- term_lift x t \: T.
Proof.
  rip; gen D G T x; induction_type t.
  match goal with
    | [ |- context[lift_le_gt_dec ?X ?Y] ] 
      => break (lift_le_gt_dec X Y); tburn;
         constructor; rewrite get_delete_above_idx in *; tburn
  end.

  econstructor. eapply IHt. rewrite delete_tenv_lift. burn.
Qed.
Hint Resolve tenv_weakening.

Lemma type_substition_preserves_typing'
  :  forall (D:kenv)(G:tenv)(X:tvar)(t:term)(U T:typ)
  ,  delete D X \\- U \: KStar
  -> D \, G ||- t \: T
  -> delete D X \, (tenv_substitute X U G) ||- [X ~~> U] t \: [X |=> U] T.
Proof.
  rip; gen D G X U T; induction_type t.

  (* TR-Nat *)
  assert (TNat = [X |=> U] TNat). burn.
  econstructor. burn. burn.

  (* TR-Abs *)
  simpl. econstructor. eapply type_substition_preserves_kinding'; burn.
  rewrite rewind_tenv_substitute. burn.

  (* TR-App *)
  econstructor. specialize (IHt1 _ _ _ _ H _ H5). simpl in IHt1. eassumption.
  eapply IHt2; burn.

  (* TR-TyAbs *)
  simpl. econstructor.
  assert (X = 0 + X) by burn. rewrite H0 at 2; clear H0.
  rewrite typ_lift_over_tenv_subs; simpl.
  rewrite delete_rewind. 
  eapply IHt; tburn.

  (* TR-TyApp *)
  rename t0 into T'. rewrite (commute_typ_subs 0 X); simpl; tburn.
  eapply TR_TyApp; tburn.
  assert (TAll ([S X |=> typ_lift 0 U] T0) = [X |=> U] TAll T0) by burn.
  rewrite H0; burn.
Qed.

Lemma type_substition_preserves_typing
  :  forall (D:kenv)(G:tenv)(t:term)(U T:typ)
  ,  D \\- U \: KStar
  -> (KStar :: D) \, G ||- t \: T 
  -> D \, (tenv_substitute 0 U G) ||- [0 ~~> U] t \: [0 |=> U] T.
Proof.
  rip; eapply (type_substition_preserves_typing' (KStar :: D) _ 0); burn.
Qed.
Hint Resolve type_substition_preserves_typing.



Lemma term_substition_preserves_typing' 
  :  forall (D:kenv)(G:tenv)(x:var)(s t:term)(U T:typ)
  ,  get G x = Some U 
  -> D \, delete G x ||- s \: U 
  -> D \, G ||- t \: T 
  -> D \, delete G x ||- [x ~> s] t \: T.
Proof.
  loosen t; induction t; opburn' tt type_rel;
  match goal with
    (* TVar *)
    | [ |- context [ nat_compare _ _ ] ] 
      => break_nat_compare; tburn; constructor; tburn
    (* TAbs *)                                              
    | [ |- context [ Abs _ _ ]         ]
      => econstructor; try rewrite delete_rewind; tburn
    (* TyAbs *)
    | [ |- context [ TyAbs _ ]         ]
      => econstructor; rewrite <- delete_tenv_lift; eapply IHt; tburn;
         rewrite delete_tenv_lift; tburn 
   end.
Qed.

Lemma term_substition_preserves_typing 
  :  forall (D:kenv)(G:tenv)(s t:term)(U T:typ)
  ,  D \, delete (U :: G) 0 ||- s \: U 
  -> D \, (U :: G) ||- t \: T 
  -> D \, delete (U :: G) 0 ||- [0 ~> s] t \: T.
Proof.
  rip; eapply term_substition_preserves_typing'; crush.
Qed.
Hint Resolve term_substition_preserves_typing.


Theorem type_preservation
  :  forall (t t':term)(T:typ)
  ,  nil \, nil ||- t \: T
  -> t ==> t'
  -> nil \, nil ||- t' \: T.
Proof.
  loosen t; induction t;
  opburn' 
    (term_substition_preserves_typing, type_substition_preserves_typing) 
    (step, type_rel).
Qed. 

Lemma nat_canonical 
  :  forall (t : term)
  ,  value t 
  -> nil \, nil ||- t \: TNat
  -> (exists n, t = (NConst n)).
Proof.
  loosen t; induction t;
  opburn' tt (type_rel, value, weak_normal).
Qed. 
Hint Resolve nat_canonical.

Lemma arrow_canonical 
  :  forall (T1 T2:typ)(t : term)
  ,  value t 
  -> nil \, nil ||- t \: (TArrow T1 T2)
  -> (exists t0, t = (Abs T1 t0)).
Proof.
  loosen t; induction t;
  opburn' tt (type_rel, value, weak_normal).
Qed.
Hint Resolve arrow_canonical.

Lemma all_canonical 
  :  forall (T:typ)(t:term)
  ,  value t 
  -> nil \, nil ||- t \: (TAll T)
  -> (exists t0, t = (TyAbs t0)).
Proof.
  loosen t; induction t;
  opburn' tt (type_rel, value, weak_normal).
Qed. 
Hint Resolve all_canonical.

Definition mark (T : Type) (x : T) := True.
Arguments mark [T] _.
(* Turn the marking into a helper tactic *)
Theorem type_progress
  :  forall (t : term)(T:typ)
  ,  nil \, nil ||- t \: T
  -> (exists t', t ==> t')
  \/ value t.
Proof.
  loosen t; induction t;
  opburn'' 
    (nat_canonical, arrow_canonical, all_canonical)
    (step, type_rel)
    ltac:(fun H =>
      match goal with
        | [ H : mark _ |- _] => fail 1
        | _ =>
            let T := fresh "T" in      
            match type of H with
              | _ \, _ ||- _ \: TArrow ?T1 ?T2 =>
                pose (T:=TArrow T1 T2) ;
                assert (mark (TArrow T1 T2)) by constructor
              | _ \, _ ||- _ \: TAll ?T1 =>
                pose (T:=TAll T1) ;
                assert (mark (TAll T1)) by constructor
            end
      end).
Qed.
