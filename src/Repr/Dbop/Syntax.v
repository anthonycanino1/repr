Require Import List.

Require Import Repr.Lists.

Require Import Repr.Tactics.All.
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

(* A few examples demonstrating the use of de Bruijn indicies *)
Example sum : term :=
  Abs (Abs (Add (Var 0) (Var 1))).

Example three_the_hard_way : term :=
  App (App sum (NConst 1)) (NConst 2).

Inductive typ : Set :=
  | TNat : typ
  | TArrow : typ -> typ -> typ .

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
    | [H : forall t', ?T1 ==> _ -> _, H1 : ?T1 ==> _ |- _ ] => extend (H _ H1); subst; simpl
  end; 
  eauto.
Qed.

(* On to typing *)

Definition free_in (G:env)(x:var) := x < length G.
Definition has_type (G:env)(x:var)(T:typ) := get G x = Some T.

Theorem free_in_implies_has_type : 
  forall G x, free_in G x -> exists T, has_type G x T.
Proof.
  unfold free_in; unfold has_type; introh Hfr; eapply (idx_lt_length _ _ _ Hfr).
Qed.

Theorem has_type_implies_free :
  forall G x T, has_type G x T -> free_in G x.
Proof.
  unfold has_type; unfold free_in; intros G x; generalize dependent G;
  induction x; introh Hht; destruct G; simpl in Hht; clean 1.
  simpl; auto with arith.
  simpl; apply lt_n_S; eapply IHx; eassumption.
Qed.


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
        has_type G x T ->
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


Lemma substition_preserves_typing' :
  forall (G:env)(x:var)(s t:term)(S T:typ),
    has_type G x S ->
    delete G x ||- s \: S ->
    G ||- t \: T ->
    delete G x ||- [x ~> s] t \: T.
Proof.
  introh Hhas_type HsT HtT; induction HtT; 
  try (constructor; spec; assumption).

  simpl. remember (nat_compare x0 x) as X; destruct X.
  assert (Eq = nat_compare x0 x -> nat_compare x0 x = Eq).
    intros. auto.
  spec.

  extend (nat_compare_eq _ _ H0).
  subst. assert (S = T).
    unfold has_type in *. rewrite Hhas_type in H. inversion H; subst. reflexivity.
    subst. auto.
 
Qed.



Lemma substition_preserves_typing : 
  forall (G:env)(x:var)(s t:term)(S T:typ),
    has_type G x S ->
    G ||- s \: S ->
    G ||- t \: T ->
    delete G x ||- [x ~> s] t \: T.
Proof.
  introh Hhas_type Hst Htt; induction Htt.

  simpl.


Qed.
    
    
    
     

        


