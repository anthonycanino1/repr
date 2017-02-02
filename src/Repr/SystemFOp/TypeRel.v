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
  linduction t; 
  opburn' kind_rel_imp_well_formed_typ tt type_rel; eauto.
Qed.

Definition marker_nOn (n:nat) := (0 + n).
Hint Unfold marker_nOn.

Lemma nOn
  :  forall (n : nat)
  ,  n = marker_nOn n.
Proof. opburn. Qed.

Lemma nOn_ONCE (n:nat) : rewrite_ONCE (nOn n).
  constructor.
Qed.

Definition mark (T : Type) (x : T) := True.
Arguments mark [T] _.

Ltac search_inner_type H :=
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
  end.

Lemma kenv_insert
  :  forall (D:kenv)(G:tenv)(t:term)(T:typ)(X:tvar)
  ,  D \, G ||- t \: T
  -> (insert D X KStar) \, (tenv_lift X G) ||- (typ_term_lift X t) \: (typ_lift X T).
Proof.
  linduction t; 
  opburn'' 
    (get_tenv_lift, kind_rel_insert)
    rewind_tenv_lift
    type_rel 
    ltac:(fun H => search_inner_type H).

  (* Abs *)
  econstructor; opburn' tt rewind_tenv_lift tt.

  (* TyAbs *)
  econstructor; opburn' tt (insert_rewind, tenv_lift_SX) tt.

  break (nat_compare X 0); norm_nat_compare; opburn.
  opburn' tt ((nOn_ONCE O), typ_lift_over_subs') tt.
  opburn' tt ((nOn_ONCE X), typ_lift_over_subs') tt.
Qed.

Lemma kenv_weakening
  :  forall (D:kenv)(G:tenv)(t:term)(T:typ)(X:tvar)
  ,  D \, G ||- t \: T
  -> (KStar :: D) \, (tenv_lift 0 G) ||- (typ_term_lift 0 t) \: (typ_lift 0 T).
Proof.
  intros; opburn' kenv_insert cons_as_insert tt.
Qed.

Lemma tenv_weakening
  :  forall (D:kenv)(G:tenv)(t:term)(T:typ)(x:var)
  ,  D \, delete G x ||- t \: T
  -> D \, G ||- term_lift x t \: T.
Proof.
  linduction t; 
  opburn' tt tt type_rel;
  match goal with
    (* T-Var *)
    | [ |- context [lift_le_gt_dec ?X ?Y] ] =>
      break (lift_le_gt_dec X Y); opburn;
        econstructor; opburn;
          [rewrite get_delete_below_idx in *; opburn |
           rewrite get_delete_above_idx in *; opburn ]
    (* T-Abs *)
    | _ => 
      econstructor;
      eapply IHt;
      opburn' (tt,tt) delete_tenv_lift tt
  end.
Qed.

Lemma type_substition_preserves_typing'
  :  forall (D:kenv)(G:tenv)(X:tvar)(t:term)(U T:typ)
  ,  delete D X \\- U \: KStar
  -> D \, G ||- t \: T
  -> delete D X \, (tenv_substitute X U G) ||- [X ~~> U] t \: [X |=> U] T.
Proof.
  linduction t;
  opburn' (tt,tt) tt type_rel; try econstructor;
  opburn'' 
    (get_tenv_substitute, type_substition_preserves_kinding')
    (rewind_tenv_substitute, typ_lift_over_subs, delete_rewind)
    tt
    ltac:(fun H => search_inner_type H);
  eauto.

  opburn' tt ((nOn_ONCE X), typ_lift_over_tenv_subs, delete_rewind) tt.    
  rewrite delete_rewind.
  eapply IHt.
  eapply kind_rel_weakening; opburn.
  opburn.
  
  opburn' tt (commute_typ_subs O X) tt.
Qed.

Lemma type_substition_preserves_typing
  :  forall (D:kenv)(G:tenv)(t:term)(U T:typ)
  ,  D \\- U \: KStar
  -> (KStar :: D) \, G ||- t \: T 
  -> D \, (tenv_substitute 0 U G) ||- [0 ~~> U] t \: [0 |=> U] T.
Proof.
  rip; eapply (type_substition_preserves_typing' (KStar :: D) _ 0); opburn.
Qed.

Lemma term_substition_preserves_typing' 
  :  forall (D:kenv)(G:tenv)(x:var)(s t:term)(U T:typ)
  ,  get G x = Some U 
  -> D \, delete G x ||- s \: U 
  -> D \, G ||- t \: T 
  -> D \, delete G x ||- [x ~> s] t \: T.
Proof.
  linduction t; opburn' tt tt type_rel;
  match goal with
  (* TVar *)
  | [ |- context [ nat_compare _ _ ] ] =>
    break_nat_compare; opburn;
      econstructor; opburn' tt (get_delete_above_idx, get_delete_below_idx) tt

  (* TAbs *)                                              
  | [ |- context [ Abs _ _ ]         ] =>
    econstructor; opburn; rewrite delete_rewind; eapply IHt; 
      try (match goal with
           | |- _ \, ?G ||- _ \: _ => 
             pose G
           end);
      opburn' tenv_weakening tt tt

  (* TyAbs *)
  | [ |- context [ TyAbs _ ]         ] =>
    econstructor; opburn;
      rewrite <- delete_tenv_lift; eapply IHt; opburn' get_tenv_lift tt tt; eauto;
        rewrite delete_tenv_lift; eapply kenv_weakening; opburn 
  end.
Qed.

Lemma term_substition_preserves_typing 
  :  forall (D:kenv)(G:tenv)(s t:term)(U T:typ)
  ,  D \, delete (U :: G) 0 ||- s \: U 
  -> D \, (U :: G) ||- t \: T 
  -> D \, delete (U :: G) 0 ||- [0 ~> s] t \: T.
Proof.
  rip; eapply term_substition_preserves_typing'; opburn.
Qed.

Theorem type_preservation
  :  forall (t t':term)(T:typ)
  ,  nil \, nil ||- t \: T
  -> t ==> t'
  -> nil \, nil ||- t' \: T.
Proof.
  loosen t; induction t;
  opburn' 
    (term_substition_preserves_typing, type_substition_preserves_typing) 
    tt
    (step, type_rel);
  match goal with
    | [ H : _ ==> _ |- _ ] => inversion H; subst; eauto
  end;
  opburn' 
    (type_substition_preserves_typing, term_substition_preserves_typing) 
    tt 
    type_rel.
Qed. 

Lemma nat_canonical 
  :  forall (t : term)
  ,  value t 
  -> nil \, nil ||- t \: TNat
  -> (exists n, t = (NConst n)).
Proof.
  linduction t; opburn' tt tt (type_rel, value, weak_normal); eauto.
Qed. 

Lemma arrow_canonical 
  :  forall (T1 T2:typ)(t : term)
  ,  value t 
  -> nil \, nil ||- t \: (TArrow T1 T2)
  -> (exists t0, t = (Abs T1 t0)).
Proof.
  linduction t; opburn' tt tt (type_rel, value, weak_normal); eauto.
Qed.

Lemma all_canonical 
  :  forall (T:typ)(t:term)
  ,  value t 
  -> nil \, nil ||- t \: (TAll T)
  -> (exists t0, t = (TyAbs t0)).
Proof.
  linduction t; opburn' tt tt (type_rel, value, weak_normal); eauto.
Qed. 

(* Turn the marking into a helper tactic *)
Theorem type_progress
  :  forall (t : term)(T:typ)
  ,  nil \, nil ||- t \: T
  -> (exists t', t ==> t')
  \/ value t.
Proof.
  linduction t;
  opburn'' 
    (nat_canonical, arrow_canonical, all_canonical)
    tt
    (step, type_rel)
    ltac:(fun H => search_inner_type H).
  Hint Resolve type_rel_imp_wellformed_term.
  Hint Resolve kind_rel_imp_well_formed_typ.
  Focus 2.
  right~.
  intuition eauto.
  Focus 2.
  right~.
  intuition eauto.
  left~.
  exists (NConst (x0 + x)). intuition.
Qed.
