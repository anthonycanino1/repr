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

Definition var := nat.


(* We formalize the simply typed lambda calculus as an operational semantics with
   de Bruijn indicies *)
Inductive term : Set :=
  | NConst : nat -> term
  | Add : term -> term -> term

  (* The pure lambda calculus *)                      
  | Var : var -> term
  | Abs : term -> term 
  | App : term -> term -> term .

Hint Constructors term.

(* A few examples demonstrating the use of de Bruijn indicies *)
Example sum : term :=
  Abs (Abs (Add (Var 0) (Var 1))).

Example three_the_hard_way : term :=
  App (App sum (NConst 1)) (NConst 2).

Inductive typ : Set :=
  | TNat : typ
  | TArrow : typ -> typ -> typ .

Hint Constructors typ.

Definition env := list typ.

(* Before we proceed further we must encode lifting and substition for de Bruijn *)
Fixpoint lift (dp:nat)(t:term) : term :=
  match t with
    | NConst n  => NConst n
    | Add t1 t2 => Add (lift dp t1) (lift dp t2)

    | Var x =>
       if (le_gt_dec dp x) then Var (S x) else Var x
    | Abs t =>
       Abs (lift (S dp) t)
    | App t1 t2 =>
       App (lift dp t1) (lift dp t2) 
   end.

Fixpoint substitute (dp:nat)(s t:term) : term :=
  match t with
    | NConst n => 
       NConst n
    | Add t1 t2 => 
       Add (substitute dp s t1) (substitute dp s t2)
    | Var x => 
       match nat_compare x dp with
         | Eq => s
         | Gt => Var (x-1)
         | Lt => Var x
       end
    | Abs t' =>
       Abs (substitute (S dp) (lift 0 s) t')
    | App t1 t2 =>
       App (substitute dp s t1) (substitute dp s t2)
  end.

Notation "'[' x '~>' s ']' t" := (substitute x s t) (at level 30).

(* Now we define our small step semantics *)

Reserved Notation "t1 '==>' t2" (at level 40).

Inductive value : term -> Prop :=
  | VNConst : 
      forall n, value (NConst n)
  | VAbs :
      forall t, value (Abs t) .

Hint Constructors value.

Inductive step : term -> term -> Prop :=
  | EAdd1 :
      forall t1 t2 t1', 
        t1 ==> t1' -> 
        Add t1 t2 ==> Add t1' t2
  | EAdd2 :
      forall n t2 t2', 
        t2 ==> t2' -> 
        Add (NConst n) t2 ==> Add (NConst n) t2'
  | EAddPlus :
      forall n1 n2,
        Add (NConst n1) (NConst n2) ==> NConst (n1+n2)
  | EApp1 :
      forall t1 t2 t1',
        t1 ==> t1' ->
        App t1 t2 ==> App t1' t2
  | EApp2 :
      forall t11 t2 t2',
        t2 ==> t2' ->
        App (Abs t11) t2 ==> App (Abs t11) t2'
  | EAppAbs :
      forall t11 v2,
        value v2 ->
        App (Abs t11) v2 ==> [0 ~> v2] t11

where "t1 '==>' t2" := (step t1 t2).

Hint Constructors step.
  
(* A couple of evaluation examples *)
Example three_the_hard_way_eval : exists t, three_the_hard_way ==> t.      
  eexists.
  eapply EApp1.
  eapply EAppAbs.
  apply VNConst.
Qed.

(* Next we define a multi step reduction *)
Reserved Notation "t1 '==>*' t2" (at level 40).

Inductive multi : term -> term -> Prop :=
  | MRefl : 
      forall t, 
        t ==>* t
  | MStep :
      forall t1 t2 t3,
        t1 ==> t2 ->
        t2 ==>* t3 ->
        t1 ==>* t3

where "t1 '==>*' t2" := (multi t1 t2).

Example three_the_hard_way_eval' : exists t, three_the_hard_way ==>* t.      
  eexists.
  eapply MStep.
    eapply EApp1.
    eapply EAppAbs.
    apply VNConst.
    simpl.
  eapply MStep.
    eapply EAppAbs.
    apply VNConst.
    simpl.
  eapply MStep.
    eapply EAddPlus.
    simpl.
  eapply MRefl.
Qed.

(* Next we prove some theorems about our evaluation relations *)
(* Note: Fairly slow; what can I do to speed things up *)
Theorem step_deterministic : 
  forall t1 t2 t3, t1 ==> t2 -> t1 ==> t3 -> t2 = t3.
Proof.
  introh Hs1; generalize dependent t3; induction Hs1; introh Hs2;
  inverts Hs2; clean 2;
  try match goal with
    | [H : forall t', ?T1 ==> _ -> _, H1 : ?T1 ==> _ |- _ ] 
      => extend (H _ H1); subst; simpl
  end; 
  eauto.
Qed.

(* On to typing *)

Reserved Notation "G '||-' t '\:' T" (at level 40).

Inductive type_rel : env -> term -> typ -> Prop :=
  | TNConst :
      forall G n,
        G ||- (NConst n) \: TNat
  | TAdd :
      forall G t1 t2,
        G ||- t1 \: TNat ->
        G ||- t2 \: TNat ->
        G ||- (Add t1 t2) \: TNat
  | TVar :
      forall G x T,
        get G x = Some T ->
        G ||- (Var x) \: T 
  | TAbs :
      forall G t T1 T2,
        (T1 :: G) ||- t \: T2 ->
        G ||- Abs t \: TArrow T1 T2
  | TApp :
      forall G t1 t2 T1 T2,
        G ||- t1 \: TArrow T1 T2 ->
        G ||- t2 \: T1 ->
        G ||- App t1 t2 \: T2

where "G '||-' t '\:' T" := (type_rel G t T).

Hint Constructors type_rel.

Ltac inverts_type :=
  repeat
    (match goal with
       | [ H: _ ||- (NConst _) \: _ |- _ ] => inverts H
       | [ H: _ ||- (Add _ _)  \: _ |- _ ] => inverts H
       | [ H: _ ||- (Var _)    \: _ |- _ ] => inverts H
       | [ H: _ ||- (Abs _)    \: _ |- _ ] => inverts H
       | [ H: _ ||- (App _ _)  \: _ |- _ ] => inverts H
     end).

Tactic Notation "induction_type" ident(t) :=
  induction t; rip; simpl; inverts_type; tburn.

Lemma env_weakening
  :  forall (G:env)(t:term)(T:typ)(x:var)
  ,  delete G x ||- t \: T
  -> G ||- lift x t \: T.
Proof.
  rip; gen G T x; induction_type t; tburn.
  break (le_gt_dec x v); tburn.
  constructor. rewrite get_delete_above_idx in H2; burn.
Qed.
Hint Resolve env_weakening.

Lemma substition_preserves_typing' 
  :  forall (G:env)(x:var)(s t:term)(U T:typ)
  ,  get G x = Some U 
  -> delete G x ||- s \: U 
  -> G ||- t \: T 
  -> delete G x ||- [x ~> s] t \: T.
Proof.
  rip; gen G x s U T; induction_type t;
  (* Burn down TVar *)
  try(
    match goal with
      | [ |- context [ nat_compare _ _ ] ] => 
        break_nat_compare;
        tburn;
        constructor;
        tburn
    end);
  (* Cleanup TAbs *)
  econstructor; rewrite delete_rewind; tburn.
Qed.

