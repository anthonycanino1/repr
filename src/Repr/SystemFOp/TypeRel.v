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

(* We define the typing relation over kind and type environments. D and G standing
   for delta and gamma resp. *)
Reserved Notation "D ',' G '||-' t '\:' T" (at level 40).

Inductive type_rel : kenv -> tenv -> term -> typ -> Prop :=
  | TR_NConst :
      forall D G n,
        D, G ||- (NConst n) \: TNat
  | TR_Add :
      forall D G t1 t2,
        D, G ||- t1 \: TNat ->
        D, G ||- t2 \: TNat ->
        D, G ||- (Add t1 t2) \: TNat
  | TR_Var :
      forall D G x T,
        get G x = Some T ->
        D, G ||- (Var x) \: T 
  | TR_Abs :
      forall D G t T1 T2,
        D, (T1 :: G) ||- t \: T2 ->
        D, G ||- Abs T1 t \: TArrow T1 T2
  | TR_App :
      forall D G t1 t2 T1 T2,
        D, G ||- t1 \: TArrow T1 T2 ->
        D, G ||- t2 \: T1 ->
        D, G ||- App t1 t2 \: T2
  | TR_TyAbs :
      forall D G t T,
        (KStar :: D), (tenv_lift 0 G) ||- t \: T ->
        D, G ||- (TyAbs t) \: TAll T
  | TR_TyApp :
      forall D G t T ty, 
        D, G ||- t \: TAll T ->
        D, G ||- (TyApp t ty) \: [0 |=> ty] T

where "D ',' G '||-' t '\:' T" := (type_rel D G t T).

Hint Constructors type_rel.

(********************************************************************)
(* On to the substitution lemmas. They have more in common with the
 * typing relation than the proof of soundness, hence, hey remain here. *)

(* Simple tactic that helps burn down the easy cases. *)
Ltac inverts_type :=
  repeat
    (match goal with
       | [ H: _,_ ||- (NConst _)   \: _ |- _ ] => inverts H
       | [ H: _,_ ||- (Add _ _)    \: _ |- _ ] => inverts H
       | [ H: _,_ ||- (Var _)      \: _ |- _ ] => inverts H
       | [ H: _,_ ||- (Abs _ _)    \: _ |- _ ] => inverts H
       | [ H: _,_ ||- (App _ _)    \: _ |- _ ] => inverts H
       | [ H: _,_ ||- (TyAbs _)    \: _ |- _ ] => inverts H
       | [ H: _,_ ||- (TyApp _ _)  \: _ |- _ ] => inverts H
     end).

(* This tactic 'usually' gets most of the inductive and easy cases
 * when we induct over the typing relation. *)
Tactic Notation "induction_type" ident(t) :=
  induction t; rip; simpl; inverts_type; tburn.

Lemma get_lift
  :  forall (G:tenv)(x:var)(T:typ)(X:tvar)
  ,  get G x = Some T
  -> get (tenv_lift X G) x = Some (typ_lift X T).
Proof.
  induction G; destruct x; rip; 
  simpl in *; try norm_some; tburn.
Qed.
Hint Resolve get_lift.

Lemma rewind_typ_lift
  :  forall (G:tenv)(T:typ)(X:tvar)
  ,  typ_lift X T :: tenv_lift X G = tenv_lift X (T :: G).
Proof. tburn. Qed.
Hint Rewrite rewind_typ_lift.

(*
Lemma le_gt_dec_S
  :  forall n m pf
  ,  left pf = le_gt_dec n m 
  -> exists pf', left pf' = le_gt_dec (S n) (S m). 
Proof. 
  rip; dep_destruct (le_gt_dec (S n) (S m)); tburn.
Qed.
Hint Resolve le_gt_dec_S. *)

Lemma typ_lift_SX
  :  forall (X Y:tvar)(T:typ)
  ,  Y <= X
  -> typ_lift Y (typ_lift X T) = typ_lift (S X) (typ_lift Y T).
Proof.
  rip; gen X Y; induction T; tburn.

  rip;
  rename t into Z;
  break Z;
  repeat(
    simpl;
    match goal with 
      | [ |- context[le_gt_dec ?X ?Y] ] =>
        break (le_gt_dec X Y)
    end;
    tburn
  ).
Qed.  

Lemma tenv_lift_SX
  :  forall (G:tenv)(X:tvar)
  ,  tenv_lift 0 (tenv_lift X G) = tenv_lift (S X) (tenv_lift 0 G).
Proof.
  induction G; rip; simpl; tburn.
  rewrite IHG; rewrite typ_lift_SX; burn.
Qed.

(* Handy tactic for burning down TVar case analysis which usually boils down
 * to repeated less than and nat compares *)
Ltac burn_tvar :=
  repeat(
    simpl;
    break_nat_compare;
    tburn;
    match goal with
      | [ |- context[le_gt_dec ?X ?Y] ] => break (le_gt_dec X Y)
    end;
    tburn
  ).

Lemma tall_injective 
  :  forall (T1 T2:typ)
  ,  T1 = T2
  -> TAll T1 = TAll T2.
Proof. burn. Qed.

Lemma typ_lift_before_subs
  :  forall (X Y:tvar)(U T:typ)
  ,  X <= Y
  -> typ_lift X ([Y |=> U] T) =  [(S Y) |=> typ_lift X U] typ_lift X T.
Proof.
  rip; gen X Y U; induction T; tburn.
  rip; burn_tvar.

  rip; simpl; eapply tall_injective.
  rewrite IHT. rewrite <- typ_lift_SX; burn. burn.
Qed.

Lemma typ_lift_after_subs
  :  forall (X Y:tvar)(U T:typ)
  ,  X > Y
  -> typ_lift X ([Y |=> U] T) =  [Y |=> typ_lift X U] typ_lift X T.
Proof.
  rip; gen X Y U; induction T; tburn.
  rip; burn_tvar.
  rename t into Z. simpl. break (le_gt_dec X (Z-1)). 
  
  
  

  

  rip; simpl; eapply tall_injective.
  rewrite IHT. rewrite <- typ_lift_SX; burn. burn.
Qed.



Hint Resolve typ_lift_before_subs.

Lemma kenv_weaking
  :  forall (D:kenv)(G:tenv)(t:term)(T:typ)(X:tvar)
  ,  delete D X, G ||- t \: T
  -> D, (tenv_lift X G) ||- (typ_term_lift X t) \: (typ_lift X T).
Proof.
  rip; gen D G T X; induction_type t.

  assert (TNat = typ_lift 0 TNat).
    burn.
  econstructor; burn.

  simpl.
  constructor. autorewrite_goal. eapply IHt. assumption.

  simpl.
  constructor.

  
  rewrite tenv_lift_SX. eapply IHt. simpl. burn.

  rename t0 into ty.

  



Qed.  

Lemma tenv_weakening
  :  forall (D:kenv)(G:tenv)(t:term)(T:typ)(x:var)
  ,  D, delete G x ||- t \: T
  -> D, G ||- term_lift x t \: T.
Proof.
  rip; gen G T x; induction_type t.
  match goal with
    | [ |- context[le_gt_dec ?X ?Y] ] 
      => break (le_gt_dec X Y); tburn;
         constructor; rewrite get_delete_above_idx in *; tburn
  end.
Qed.
Hint Resolve env_weakening.

Lemma tm_substition_preserves_typing' 
  :  forall (G:env)(x:var)(s t:term)(U T:typ)
  ,  get G x = Some (term,U) 
  -> delete G x ||- s \: U 
  -> G ||- t \: T 
  -> delete G x ||- [x ~> s] t \: T.
Proof.
  rip; gen G x s U T; induction_type t;
  match goal with
    (* TVar *)
    | [ |- context [ nat_compare _ _ ] ] 
      => break_nat_compare; tburn; constructor; tburn
    (* TAbs *)                                              
    | [ |- context [ Abs _ ]           ]
      => econstructor; rewrite delete_rewind; tburn
  end.
Qed.

Lemma tm_substition_preserves_typing 
  :  forall (G:env)(s t:term)(U T:typ)
  ,  delete ((term,U) :: G) 0 ||- s \: U 
  -> ((term,U) :: G) ||- t \: T 
  -> delete ((term,U) :: G) 0 ||- [0 ~> s] t \: T.
Proof.
  rip; eapply tm_substition_preserves_typing'; tburn. 
Qed.




