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
Definition env := list typ.

Inductive term : Set :=
  | NConst : nat -> term
  | Add : term -> term -> term

  (* The pure lambda calculus *)                      
  | Var : var -> term
  | Abs : typ -> term -> term 
  | App : term -> term -> term 

  (* System F Extn *)
  | TyAbs : term -> term
  | TyApp : term -> typ -> term .
                            
Hint Constructors term.

Example id_tm := (TyAbs (Abs (TVar 0) (Var 0))).

Fixpoint tm_lift (dp:nat)(t:term) : term :=
  match t with
    | NConst n =>
       NConst n
    | Add t1 t2 =>
       Add (tm_lift dp t1) (tm_lift dp t2)
    | Var x =>
       if (le_gt_dec dp x) then Var (S x) else Var x
    | Abs ty t =>
       Abs ty (tm_lift (S dp) t)
    | App t1 t2 =>
       App (tm_lift dp t1) (tm_lift dp t2) 
    | TyAbs t =>
       TyAbs (tm_lift dp t)
    | TyApp t ty =>
       TyApp (tm_lift dp t) ty
   end.

Fixpoint tm_substitute (x:var)(s t:term) : term :=
  match t with
    | NConst n => 
       NConst n
    | Add t1 t2 => 
       Add (tm_substitute x s t1) (tm_substitute x s t2)
    | Var y => 
       match nat_compare y x with
         | Eq => s
         | Gt => Var (y-1)
         | Lt => Var y
       end
    | Abs ty t' =>
       Abs ty (tm_substitute (S x) (tm_lift 0 s) t')
    | App t1 t2 =>
       App (tm_substitute x s t1) (tm_substitute x s t2)
    | TyAbs t' =>
       TyAbs (tm_substitute x s t')
    | TyApp t' ty =>
       TyApp (tm_substitute x s t') ty
  end.


Fixpoint ty_tm_lift (dp:nat)(t:term) : term :=
  match t with
    | NConst n =>
       NConst n
    | Add t1 t2 =>
       Add (ty_tm_lift dp t1) (ty_tm_lift dp t2)
    | Var x =>
       Var x
    | Abs ty t =>
       Abs (ty_lift dp ty) ((ty_tm_lift dp) t)
    | App t1 t2 =>
       App (ty_tm_lift dp t1) (ty_tm_lift dp t2) 
    | TyAbs t =>
       TyAbs (ty_tm_lift (S dp) t)
    | TyApp t ty =>
       TyApp (ty_tm_lift dp t) (ty_lift dp ty)
   end.

Fixpoint ty_tm_substitute (X:tvar)(S:typ)(t:term) : term :=
  match t with
    | NConst n => 
       NConst n
    | Add t1 t2 => 
       Add (ty_tm_substitute X S t1) (ty_tm_substitute X S t2)
    | Var y => 
       Var y
    | Abs ty t' =>
       Abs (ty_substitute X S ty) (ty_tm_substitute X S t')
    | App t1 t2 =>
       App (ty_tm_substitute X S t1) (ty_tm_substitute X S t2)
    | TyAbs t' =>
       TyAbs (ty_tm_substitute X S t')
    | TyApp t' ty =>
       TyApp (ty_tm_substitute X S t') (ty_substitute X S ty)
  end.

Fixpoint env_substitute (X:tvar)(U:typ)(G:env) : env :=
  match G with
    | nil           => nil
    | (tag,T) :: G' => (tag, (ty_substitute X U T)) :: env_substitute X U G'
  end.

Fixpoint env_lift (dp:nat)(G:env) : env :=
  match G with
    | nil     => nil
    | (tag,T) :: G' => (tag, ty_lift dp T) :: env_lift dp G'
  end.

Notation "'[' x '~>' s ']' t" := (tm_substitute x s t) (at level 30).
Notation "'[' X '~~>' S ']' t" := (ty_tm_substitute X S t) (at level 30).
Notation "'[' X '^>' S ']' T" := (ty_substitute X S T) (at level 30).
Notation "'[' X '^^>' S ']' G" := (env_substitute X S G) (at level 30).

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

Inductive well_formed : env -> term -> Prop :=
  | Wf_NConst :
      forall G n, 
        well_formed G (NConst n)
  | Wf_Add :
      forall G t1 t2,
        well_formed G t1 -> well_formed G t2 -> well_formed G (Add t1 t2)
  | Wf_Var :
      forall G x T,
        get G x = Some (term,T) -> well_formed G (Var x)
  | Wf_Abs :
      forall G ty t T,
        well_formed ((term,T) :: G) t -> well_formed G (Abs ty t)
  | Wf_App :
      forall G t1 t2,
        well_formed G t1 -> well_formed G t2 -> well_formed G (App t1 t2) 
  | Wf_TyAbs :
      forall G t X,
        well_formed ((typ,TVar X) :: G) t -> well_formed G (TyAbs t)
  | Wf_TyApp :
      forall G X t ty,
        get G X = Some (typ,TVar X) ->
        well_formed G t -> well_formed G (TyApp t ty).

Hint Constructors well_formed.

Definition closed (t:term) : Prop := well_formed nil t.
Definition value (t:term)  : Prop := weak_normal t /\ closed t.

Hint Unfold closed.
Hint Unfold value.

Reserved Notation "t1 '==>' t2" (at level 40).

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
      forall ty11 t11 t2 t2',
        t2 ==> t2' ->
        App (Abs ty11 t11) t2 ==> App (Abs ty11 t11) t2'
  | EAppAbs :
      forall ty11 t11 v2,
        value v2 ->
        App (Abs ty11 t11) v2 ==> [0 ~> v2] t11
  | ETyApp :
      forall t t' ty,
        t ==> t' ->
        TyApp t ty ==> TyApp t' ty
  | ETyAppAbs :
      forall t11 ty,
        TyApp (TyAbs t11) ty ==> [0 ~~> ty] t11 

where "t1 '==>' t2" := (step t1 t2).

Hint Constructors step.

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

Hint Constructors multi.


Theorem step_deterministic : 
  forall t1 t2 t3, t1 ==> t2 -> t1 ==> t3 -> t2 = t3.
Proof.
  Admitted. (*p

  introh Hs1; generalize dependent t3; induction Hs1; introh Hs2;
  inverts Hs2; clean 2;
  try match goal with
    | [H : forall t', ?T1 ==> _ -> _, H1 : ?T1 ==> _ |- _ ] 
      => extend (H _ H1); subst; simpl
  end; 
  eauto.
Qed.*)

(* On to typing *)

Reserved Notation "G '||-' t '\:' T" (at level 40).

Inductive type_rel : env -> term -> typ -> Prop :=
  | TR_NConst :
      forall G n,
        G ||- (NConst n) \: TNat
  | TR_Add :
      forall G t1 t2,
        G ||- t1 \: TNat ->
        G ||- t2 \: TNat ->
        G ||- (Add t1 t2) \: TNat
  | TR_Var :
      forall G x T,
        get G x = Some (term,T) ->
        G ||- (Var x) \: T 
  | TR_Abs :
      forall G t T1 T2,
        ((term,T1) :: G) ||- t \: T2 ->
        G ||- Abs T1 t \: TArrow T1 T2
  | TR_App :
      forall G t1 t2 T1 T2,
        G ||- t1 \: TArrow T1 T2 ->
        G ||- t2 \: T1 ->
        G ||- App t1 t2 \: T2
  | TR_TyAbs :
      forall G t T,
        ((typ,0) :: G) ||- t \: T ->
        G ||- (TyAbs t) \: TAll T
  | TR_TyApp :
      forall G t T ty, 
        G ||- t \: TAll T ->
        G ||- (TyApp t ty) \: [0 ^> ty] T

where "G '||-' t '\:' T" := (type_rel G t T).

Hint Constructors type_rel.

(* Some type testing *)

Example tc_z  
  :   nil 
  ||- TyAbs (Abs (TArrow (TVar 0) (TVar 0)) (Abs (TVar 0) (Var 0))) 
  \:  TAll (TArrow 
                 (TArrow (TVar 0) (TVar 0)) 
                 (TArrow (TVar 0) (TVar 0)))
  .
  repeat econstructor; eauto.
Qed.

Example tc_s  
  :   nil 
  ||- TyAbs (Abs (TArrow (TVar 0) (TVar 0)) (Abs (TVar 0) (App (Var 1) (Var 0)))) 
  \:  TAll (TArrow 
                 (TArrow (TVar 0) (TVar 0)) 
                 (TArrow (TVar 0) (TVar 0)))
  .
  repeat econstructor; eauto.
Qed.

Ltac inverts_type :=
  repeat
    (match goal with
       | [ H: _ ||- (NConst _)   \: _ |- _ ] => inverts H
       | [ H: _ ||- (Add _ _)    \: _ |- _ ] => inverts H
       | [ H: _ ||- (Var _)      \: _ |- _ ] => inverts H
       | [ H: _ ||- (Abs _ _)    \: _ |- _ ] => inverts H
       | [ H: _ ||- (App _ _)    \: _ |- _ ] => inverts H
       | [ H: _ ||- (TyAbs _)    \: _ |- _ ] => inverts H
       | [ H: _ ||- (TyApp _ _)  \: _ |- _ ] => inverts H
     end).

Tactic Notation "induction_type" ident(t) :=
  induction t; rip; simpl; inverts_type; tburn.

Lemma env_weakening
  :  forall (G:env)(t:term)(T:typ)(x:var)
  ,  delete G x ||- t \: T
  -> G ||- tm_lift x t \: T.
Proof.
  rip; gen G T x; induction_type t;
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

Lemma ty_substition_preserves_typing' 
  :  forall (G G1 G2:env)(Y X:var)(t:term)(T U:typ)
  ,  get_split G Y = Some ((typ,TVar X),G1,G2)
  -> (G1 ++ ((typ,TVar X) :: G2)) ||- t \: T 
  -> (G1 ++ (delete ((typ,TVar X) :: ([X ^^> U] G2)) 0)) ||- [X ~~> U] t \: [X ^> U] T.
Proof.
  rip; gen G X t U T; induction t.
  Focus 3.
  
  







  
  

Qed.


Theorem type_preservation 
  : forall (t t':term)(T:typ)
  ,  nil ||- t \: T
  -> t ==> t'
  -> nil ||- t' \: T.     
Proof.
  rip. gen T t'; induction t; introh Htyp Heval;
  inverts Htyp; inverts Heval;
  match goal with
    | [ |- context[tm_substitute _ _ _] ] 
      => inverts H2;
         extend (substition_preserves_typing nil t2 t11 T1 T);
         simpl in Hextend;
         apply Hextend; burn
    | _ => tburn
  end.
Qed.
Hint Resolve type_preservation.

Theorem multi_type_preservation
  : forall (t t':term)(T:typ)
  ,  nil ||- t \: T
  -> t ==>* t'
  -> nil ||- t' \: T.     
Proof.
  introh Htyp Hmult; induction Hmult; burn.
Qed.

Lemma canonical_forms
  :  forall (G:env)(t:term)
  ,  value t
  (* NConst*)
  -> (G ||- t \: TNat -> exists n, t = NConst n)
  (* Abs *)
  \/ (forall T1 T2
     ,  G ||- t \: TArrow T1 T2 
     -> exists t', (T1 :: G) ||- t' \: T2 /\ t = Abs t').
Proof.
  rip. unfold value in H. 
  inversion H. unfold closed in H1.
  inverts H0.

  burn.
  inverts H1; burn.
  inverts H1.
  right~.

  rip. unfold closed in H2. inverts H0. exists t0. burn.
Qed.

Lemma nat_canonical_form
  :  forall (G:env)(t:term)
  ,  value t 
  -> G ||- t \: TNat 
  -> exists n, t = NConst n.
Proof.
  rip. unfold value in H. inversion H. unfold closed in H2.
  inverts H1.
  burn. clean 2. clean 2.
Qed.    
 
Lemma abs_canonical_form
  :  forall (G:env)(t:term)
  ,  value t
  -> (forall T1 T2
     ,  G ||- t \: TArrow T1 T2 
     -> exists t', (T1 :: G) ||- t' \: T2 /\ t = Abs t').
Proof.
  rip. unfold value in H. inverts H. unfold closed in H2.
  inverts H0. clean 2. inverts H2. burn. clean 2.
Qed.

Lemma well_typed_imp_well_formed
  :  forall (G:env)(t:term)(T:typ)
  ,  G ||- t \: T
  -> well_formed G t.
Proof.
  rip; gen G T; induction_type t.
Qed.

Theorem type_progress
  :  forall (t:term)(T:typ)
  ,  nil ||- t \: T
  -> value t
  \/ exists t', t ==> t'.
Proof.
  induction_type t.
  specialize (IHt1 TNat H3). specialize (IHt2 TNat H5).
  inverts IHt1; inverts IHt2; tburn.

  extend (nat_canonical_form nil t1 H H3). inverts Hextend.
  extend (nat_canonical_form nil t2 H0 H5). inverts Hextend.
  burn.
  extend (nat_canonical_form nil t1 H H3). inverts Hextend.
  burn.

  left~. unfold value. split~; tburn. unfold closed.
  econstructor. 

  eapply well_typed_imp_well_formed. eassumption.

  specialize (IHt1 _ H3). specialize (IHt2 _ H5).

  inverts IHt1; inverts IHt2; tburn.
  extend (abs_canonical_form nil t1 H T1 T H3).
  inverts Hextend. inverts H1. burn.
  extend (abs_canonical_form nil t1 H T1 T H3). 
  inverts Hextend. inverts H1. burn.
Qed.
Hint Resolve type_progress.

Theorem type_soundness
  :  forall (t:term)(T:typ)
  ,  nil ||- t \: T
  -> value t 
  \/ exists t', t ==> t' /\ nil ||- t' \: T.
Proof.
  introh Htyp; extend (type_progress t T Htyp); burn.
Qed.

Theorem multi_type_soundness
  :  forall (t:term)(T:typ)
  ,  nil ||- t \: T
  -> exists t', t ==>* t' /\ value t' /\ nil ||- t' \: T.
Proof.
  rip.


  
  










  
  

                                              
                                            