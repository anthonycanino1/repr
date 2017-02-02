Require Import List.

Require Import Repr.Lists.

Require Import Repr.Tactics.All.
Require Import Repr.Tactics.Rewrite.
Require Import Repr.Tactics.Burn.
Require Import Repr.Tactics.Norm.
Require Import Repr.Tactics.LibTactics.
Require Import Repr.Tactics.Opburn.

Require Import Coq.Arith.Peano_dec.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.Lt.

Require Import Repr.SystemFOp.Kind.
Require Import Repr.SystemFOp.Type.

(* Using var for a de bruijn index states our intent better than nat does *)
Definition var := nat.

Inductive term : Set :=
  | NConst : nat -> term
  | Add    : term -> term -> term
  | Var    : var -> term
  | Abs    : typ -> term -> term 
  | App    : term -> term -> term 
  | TyAbs  : term -> term
  | TyApp  : term -> typ -> term .
Hint Constructors term.

(* Unfortunately, formalizing System F in Coq means we cannot simply overload 
 * lifting and substition for types over terms. This gets ugly and tedious. *)
Fixpoint typ_term_lift (dp:nat)(t:term) : term :=
  match t with
    | NConst n =>
       NConst n
    | Add t1 t2 =>
       Add (typ_term_lift dp t1) (typ_term_lift dp t2)
    | Var x =>
       Var x
    | Abs ty t =>
       Abs (typ_lift dp ty) ((typ_term_lift dp) t)
    | App t1 t2 =>
       App (typ_term_lift dp t1) (typ_term_lift dp t2) 
    | TyAbs t =>
       TyAbs (typ_term_lift (S dp) t)
    | TyApp t ty =>
       TyApp (typ_term_lift dp t) (typ_lift dp ty)
   end.

Fixpoint typ_term_substitute (X:tvar)(U:typ)(t:term) : term :=
  match t with
    | NConst n => 
       NConst n
    | Add t1 t2 => 
       Add (typ_term_substitute X U t1) (typ_term_substitute X U t2)
    | Var x => 
       Var x
    | Abs ty t' =>
       Abs (typ_substitute X U ty) (typ_term_substitute X U t')
    | App t1 t2 =>
       App (typ_term_substitute X U t1) (typ_term_substitute X U t2)
    | TyAbs t' =>
       TyAbs (typ_term_substitute (S X) (typ_lift 0 U) t')
    | TyApp t' ty =>
       TyApp (typ_term_substitute X U t') (typ_substitute X U ty)
  end.

(* Some notation to make our lives easier. *)
Notation "'[' X '~~>' U ']' t" := (typ_term_substitute X U t) (at level 30).


(* Standard de bruijn lifting and substitution operations over terms *)
Fixpoint term_lift (dp:nat)(t:term) : term :=
  match t with
    | NConst n =>
       NConst n
    | Add t1 t2 =>
       Add (term_lift dp t1) (term_lift dp t2)
    | Var x =>
       if (lift_le_gt_dec dp x) then Var (S x) else Var x
    | Abs ty t =>
       Abs ty (term_lift (S dp) t)
    | App t1 t2 =>
       App (term_lift dp t1) (term_lift dp t2) 
    | TyAbs t =>
       TyAbs (term_lift dp t)
    | TyApp t ty =>
       TyApp (term_lift dp t) ty
   end.

Fixpoint term_substitute (x:var)(s t:term) : term :=
  match t with
    | NConst n => 
       NConst n
    | Add t1 t2 => 
       Add (term_substitute x s t1) (term_substitute x s t2)
    | Var y => 
       match nat_compare y x with
         | Eq => s
         | Gt => Var (y-1)
         | Lt => Var y
       end
    | Abs ty t' =>
       Abs ty (term_substitute (S x) (term_lift 0 s) t')
    | App t1 t2 =>
       App (term_substitute x s t1) (term_substitute x s t2)
    | TyAbs t' =>
       TyAbs (term_substitute x (typ_term_lift 0 s) t')
    | TyApp t' ty =>
       TyApp (term_substitute x s t') ty
  end.

(* Some notation to make our lives easier. *)
Notation "'[' x '~>' s ']' t" := (term_substitute x s t) (at level 30).

(* We define a weak normal form for terms. *)
Inductive weak_normal : term -> Prop :=
  | WN_NConst : 
      forall n, weak_normal (NConst n)
  | WN_Var :
      forall x, weak_normal (Var x)
  | WN_Abs :
      forall t ty, weak_normal (Abs ty t) 
  | WN_TyAbs :
      forall t, weak_normal (TyAbs t).
Hint Constructors weak_normal.

(* Terms are well formed with respect to a kind environment and type environment. 
 * Note that the tricky part is lifting the type environment when a new kind is
 * pushed onto the kind environment in the TyAbs case. *)
Inductive well_formed_term : kenv -> tenv -> term -> Prop :=
  | WF_NConst :
      forall D G n, 
        well_formed_term D G (NConst n)
  | WF_Add :
      forall D G t1 t2,
        well_formed_term D G t1 -> 
        well_formed_term D G t2 -> 
        well_formed_term D G (Add t1 t2)
  | WF_Var :
      forall D G x T,
        get G x = Some T -> 
        well_formed_term D G (Var x)
  | WF_Abs :
      forall D G ty t T,
        well_formed_typ D ty ->
        well_formed_term D (T :: G) t -> 
        well_formed_term D G (Abs ty t)
  | WF_App :
      forall D G t1 t2,
        well_formed_term D G t1 -> 
        well_formed_term D G t2 ->
        well_formed_term D G (App t1 t2) 
  | WF_TyAbs :
      forall D G t,
        well_formed_term (KStar :: D) (tenv_lift 0 G) t ->
        well_formed_term D G (TyAbs t)
  | WF_TyApp :
      forall D G t ty,
        well_formed_typ D ty ->
        well_formed_term D G t ->
        well_formed_term D G (TyApp t ty) .
Hint Constructors well_formed_term.

(* A term is closed if it is well-formed in the empty kind and type environments. *)
Definition closed (t:term) : Prop := well_formed_term nil nil t.
Hint Unfold closed.

(* A closed term is a value if it is in weak normal form. *)
Definition value (t:term)  : Prop := weak_normal t /\ closed t.
Hint Unfold value.

(********************************************************************)
(* We define operational semantics for terms here, and leave the typing
 * relation to TypeRel.v *)



(* We define a small-step semantics for System F. I prefer a notational definition
 * when it is obviously what we mean; hence, the '==>'. *)
Reserved Notation "t1 '==>' t2" (at level 40).

Inductive step : term -> term -> Prop :=
  | E_Add1 :
      forall t1 t2 t1', 
        t1 ==> t1' -> 
        Add t1 t2 ==> Add t1' t2
  | E_Add2 :
      forall n t2 t2', 
        t2 ==> t2' -> 
        Add (NConst n) t2 ==> Add (NConst n) t2'
  | E_AddPlus :
      forall n1 n2,
        Add (NConst n1) (NConst n2) ==> NConst (n1+n2)
  | E_App1 :
      forall t1 t2 t1',
        t1 ==> t1' ->
        App t1 t2 ==> App t1' t2
  | E_App2 :
      forall ty11 t11 t2 t2',
        t2 ==> t2' ->
        App (Abs ty11 t11) t2 ==> App (Abs ty11 t11) t2'
  | E_AppAbs :
      forall ty11 t11 v2,
        value v2 ->
        App (Abs ty11 t11) v2 ==> [0 ~> v2] t11
  | E_TyApp :
      forall t t' ty,
        t ==> t' ->
        TyApp t ty ==> TyApp t' ty
  | E_TyAppAbs :
      forall t11 ty,
        TyApp (TyAbs t11) ty ==> [0 ~~> ty] t11 

where "t1 '==>' t2" := (step t1 t2).

Hint Constructors step.

(* We define a multi step relation mostly for playing around with examples. *)
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

Hint Constructors multi.

(********************************************************************)
