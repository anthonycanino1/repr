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




