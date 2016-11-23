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

(* Looks better to use a 'tvar' over a nat for a de bruijn index *)
Definition tvar := nat.

(* TVars are indexes into a kind environment. We use TNat as our base type. *)
Inductive typ : Set :=
  | TVar   : tvar -> typ
  | TNat   : typ
  | TArrow : typ -> typ -> typ 
  | TAll   : typ -> typ .

Hint Constructors typ.

(* Types are well-formed with respect to a kind environment. *)
Inductive well_formed_typ : kenv -> typ -> Prop :=
  | WFT_TVar : 
      forall D X, 
        (exists K, get D X = Some K) -> 
        well_formed_typ D (TVar X)
  | WFT_TNat :
      forall D, 
        well_formed_typ D TNat
  | WFT_TArrow :
      forall D T1 T2, 
        well_formed_typ D T1 ->
        well_formed_typ D T2 ->
        well_formed_typ D (TArrow T1 T2)
  | WFT_TAll :
      forall D K T,
        well_formed_typ (K :: D) T ->
        well_formed_typ D (TAll T) .

Hint Constructors well_formed_typ.

(* A type is closed if it is well-formed in the empty kind environment *)
Definition closed_typ (T:typ) : Prop := well_formed_typ nil T.

(* Standard de bruijn lifting and substituion functions operating at the type level *)
Fixpoint typ_lift (dp:nat)(T:typ) : typ :=
  match T with
    | TVar X =>
       if (le_gt_dec dp X) then TVar (S X) else TVar X
    | TNat => 
       TNat
    | TArrow T1 T2 =>
       TArrow (typ_lift dp T1) (typ_lift dp T2)
    | TAll T' =>
       TAll (typ_lift (S dp) T')
  end.

Fixpoint typ_substitute (X:tvar)(U T:typ) : typ :=
  match T with
    | TVar Y =>
       match nat_compare Y X with
         | Eq => U
         | Gt => TVar (Y-1)
         | Lt => TVar Y
       end
    | TNat =>
       TNat
    | TArrow T1 T2 =>
       TArrow (typ_substitute X U T1) (typ_substitute X U T2)
    | TAll T' =>
       TAll (typ_substitute (S X) (typ_lift 0 U) T')
  end.

Notation "'[' X '|=>' U ']' T" := (typ_substitute X U T) (at level 30).

(********************************************************************)
(* We must define a Kind Judgement for Types *)

Reserved Notation "D '\\-' T \: K" (at level 30).

Inductive kind_rel : kenv -> typ -> kind -> Prop :=
  | KR_TVar :
      forall D X K,
        get D X = Some K ->
        D \\- TVar X \: K
  | KR_TNat :
      forall D,
        D \\- TNat \: KStar
  | KR_TArrow :
      forall D T1 T2,
        D \\- T1 \: KStar ->
        D \\- T2 \: KStar ->
        D \\- TArrow T1 T2 \: KStar
  | KR_TAll :
      forall D T,
        (KStar :: D) \\- T \: KStar ->
        D \\- TAll T \: KStar 

where "D '\\-' T \: K" := (kind_rel D T K).

Hint Constructors kind_rel.

(* A couple of useful Lemma's --- I am cheating though, I saw these
   from Iron Lambda *)

(* Simple tactic that helps burn down the easy cases. *)
Ltac inverts_typ :=
  repeat
    (match goal with
       | [ H: _ \\- (TVar _)     \: _ |- _ ] => inverts H
       | [ H: _ \\- TNat         \: _ |- _ ] => inverts H
       | [ H: _ \\- (TArrow _ _) \: _ |- _ ] => inverts H
       | [ H: _ \\- (TAll _)     \: _ |- _ ] => inverts H
     end).

(* This tactic 'usually' gets most of the inductive and easy cases
 * when we induct over the typing relation. *)
Tactic Notation "induction_kind" ident(t) :=
  induction t; rip; simpl; inverts_typ; tburn.

(* A well-kinded type is well-formed *)
Lemma kind_rel_imp_well_formed_typ
  :  forall D T K
  ,  D \\- T \: K
  -> well_formed_typ D T.
Proof.
  rip; gen D K; induction_kind T.
Qed.

(* We may insert into a kind environment at X provided we lift all
 * types that occuring after X in the kind environment. 
 *
 * NOTE: This attempt at automation shows where the burn tactic fails,
 * and one area where crush does well. Specifically, burn doesn't do
 * a great job with rewriting after constructors are needed.
 *
 * It is tricky --- If you rewrite too soon or too late you will block
 * the resolution process. Something I want to return to and study. *)
Lemma kind_rel_insert
  :  forall D T K X
  ,  D \\- T \: K
  -> insert D X KStar \\- typ_lift X T \: K.
Proof.
  Hint Rewrite insert_rewind.
  rip; gen D K X; induction_kind T;
  match goal with
    (* TVar *)
    | [ |- context [le_gt_dec ?A ?B] ] 
      => break (le_gt_dec A B); tburn
    (* TAbs *)
    | _ 
      => econstructor; autorewrite_goal; burn
  end.
  Remove Hints insert_rewind.
Qed.
Hint Resolve kind_rel_insert.

Lemma cons_eq_insert0
  :  forall X (ls: list X)(e:X)
  ,  e :: ls = insert ls 0 e.
Proof.
  destruct ls; burn.
Qed.  

Theorem kind_rel_weakening
  :  forall D T K
  ,  D \\- T \: K
  -> (KStar :: D) \\- typ_lift 0 T \: K.
Proof.
  rip; rewrite cons_eq_insert0; burn.
Qed.  

(********************************************************************)
(* Lemmas for manipulating the lifting and substitution operations. *)

(* Handy tactic for burning down TVar case analysis which usually boils down
 * to repeated less than and nat compares *)
Ltac burn_tvar :=
  repeat(
    simpl;
    try break_nat_compare;
    tburn;
    match goal with
      | [ |- context[le_gt_dec ?X ?Y] ] => break (le_gt_dec X Y)
    end;
    tburn
  ).

Ltac case_lift :=
  match goal with
    | [ |- context [le_gt_dec ?a ?b] ] =>
      case (le_gt_dec a b)
  end.

Lemma typ_subs_nil_typ_lift
  :  forall X U T
  ,  [X |=> U] (typ_lift X T) = T.
Proof.
  rip; gen X U; induction_kind T; destruct X;
  case_lift; burn_tvar. 
Qed.
Hint Rewrite typ_subs_nil_typ_lift.

Lemma tall_injective 
  :  forall (T1 T2:typ)
  ,  T1 = T2
  -> TAll T1 = TAll T2.
Proof. burn. Qed.

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

Lemma typ_lift_over_subs
  :  forall (n n':nat)(U T:typ)
  ,  typ_lift n ([(n + n') |=> U] T) 
  =  [(1 + n + n') |=> typ_lift n U] typ_lift n T.
Proof.
  rip; gen n n' U; induction T; tburn.
  rip; burn_tvar.

  rip; simpl; eapply tall_injective.
  assert (S (n + n') = S n + n'). burn. rewrite H. rewrite IHT. simpl.
  

  rewrite <- typ_lift_SX; burn. 
Qed.
Hint Rewrite typ_lift_over_subs.

(* LAST *)

Lemma typ_lift_over_subs'
  :  forall (n n':nat)(U T:typ)
  ,  typ_lift (n + n') ([n |=> U] T) 
  =  [n  |=> typ_lift (n + n') U] typ_lift (1 + n + n') T.
Proof.
  rip; gen n n' U; induction T; tburn.


Qed.
Hint Rewrite typ_lift_over_subs.

(********************************************************************)

(* We define type environments and some operations over them here. *)
Definition tenv := list typ.
Hint Unfold tenv.

(* We will need to lift and substitute over type environments when
 * new type variables are 'pushed' *)
Definition tenv_lift (dp:nat)(G:tenv) : tenv := 
  map (typ_lift dp) G.
Hint Unfold tenv_lift.

Definition tenv_substitute (X:tvar)(U:typ)(G:tenv) : tenv := 
  map (typ_substitute X U) G.
Hint Unfold tenv_substitute.



