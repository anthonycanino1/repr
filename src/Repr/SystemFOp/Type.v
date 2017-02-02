Require Import List.

Require Import Repr.Lists.

Require Import Repr.Tactics.
Require Import Repr.Tactics.LibTactics.
Require Import Repr.Tactics.Opburn.

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
      forall D T,
        (exists K, well_formed_typ (K :: D) T) ->
        well_formed_typ D (TAll T) .

Hint Constructors well_formed_typ.

(* A type is closed if it is well-formed in the empty kind environment *)
Definition closed_typ (T:typ) : Prop := well_formed_typ nil T.

(* Trick to control how far simpl goes for better automation *)
Definition lift_le_gt_dec (n m : nat) := le_gt_dec n m.
Arguments lift_le_gt_dec _ _ : simpl nomatch.

(* Standard de bruijn lifting and substituion functions operating at the type level *)
Fixpoint typ_lift (dp:nat)(T:typ) : typ :=
  match T with
    | TVar X =>
       if (lift_le_gt_dec dp X) then TVar (S X) else TVar X
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


(********************************************************************)
(* Lemmas for manipulating the lifting and substitution operations. *)

(* Handy tactic for burning down TVar case analysis which usually boils down
 * to repeated less than and nat compares *)

Ltac case_lift :=
  match goal with
    | [ |- context [lift_le_gt_dec ?a ?b] ] =>
      case (lift_le_gt_dec a b)
  end.

(* Mega tactic that deals with all the de bruijn comparisons *)
Ltac burn_tvar :=
  simpl;
  match goal with
    | [ |- context[nat_compare _ _ ] ]
      => break_nat_compare ;
         opburn ;
         burn_tvar
    | [ |- context[ match nat_compare ?n ?m with 
                      | Eq => _ 
                      | Lt => _ 
                      | Gt => _  
                    end ] ]
      => break (nat_compare n m) ;
         norm_nat_compare ;
         opburn ;
         burn_tvar 
    | [ |- context [lift_le_gt_dec _ _ ] ]
      => case_lift ;
         opburn ;
         burn_tvar
     | [ |- context [ match ?n with O => _ | S _ => _ end ] ] 
       => destruct n ;
          opburn ;
          burn_tvar
    | _ 
      => opburn
  end.

Lemma typ_subs_nil_typ_lift
  :  forall X U T
  ,  [X |=> U] (typ_lift X T) = T.
Proof.
  linduction T; destruct X; opburn' tt tt kind_rel; burn_tvar.
Qed.

Lemma typ_lift_SX
  :  forall (X Y:tvar)(T:typ)
  ,  Y <= X
  -> typ_lift (S X) (typ_lift Y T) = typ_lift Y (typ_lift X T).
Proof.
  linduction T; opburn' tt tt kind_rel; burn_tvar.
Qed.

Definition marker_Snm (n n':nat) := S n + n'.
Hint Unfold marker_Snm.

Lemma Snm_Snpm 
  :  forall (n m : nat)
  ,  S (n + m) = marker_Snm n m.
Proof. opburn. Qed.

Lemma typ_lift_over_subs
  :  forall (n n':nat)(U T:typ)
  ,  typ_lift n ([(n + n') |=> U] T) 
  =  [(1 + n + n') |=> typ_lift n U] typ_lift n T.
Proof.
  linduction T; 
  opburn' 
    tt 
    (typ_lift_SX, Snm_Snpm) 
    kind_rel; 
  [burn_tvar].
Qed.

Lemma typ_lift_over_subs'
  :  forall (n n':nat)(U T:typ)
  ,  typ_lift (n + n') ([n |=> U] T) 
  =  [n  |=> typ_lift (n + n') U] typ_lift (1 + n + n') T.
Proof.
  linduction T;
  opburn'
    tt
    (typ_lift_SX, Snm_Snpm)
    kind_rel;
  [burn_tvar].
Qed.

Definition marker_Onm (n n':nat) := O + (n + n').
Hint Unfold marker_Onm.

Lemma Onm 
  :  forall (n m : nat)
  ,  (n + m) = marker_Onm n m.
Proof. opburn. Qed.

Lemma Onm_ONCE : rewrite_ONCE (Onm).
  constructor.
Qed.

(* LAST *)
(* Coq tuples are right associative, we need our own notation *)



Lemma commute_typ_subs
  :  forall (n n':nat)(T1 T2 T3:typ)
  ,  [n + n' |=> T3] ([n |=> T2] T1)
  =  [n |=> [ n + n' |=> T3] T2 ] ([1 + n + n' |=> (typ_lift n T3)] T1).
Proof.
  linduction T1; 
  opburn' 
    tt 
    (Onm_ONCE, Snm_Snpm, typ_lift_SX, typ_lift_over_subs)
    kind_rel;
  [burn_tvar];
  opburn' tt typ_subs_nil_typ_lift tt.
Qed.

(********************************************************************)

(* A well-kinded type is well-formed *)
Lemma kind_rel_imp_well_formed_typ
  :  forall D T K
  ,  D \\- T \: K
  -> well_formed_typ D T.
Proof.
  linduction T; opburn' tt tt kind_rel; eauto.
Qed.

(* NOTE: inster will fall on polymorphic types, but we can make it work
   by trying to *type of* all H's on the goal. *)
(* One dirty trick due to K's rewrite *)
Lemma kind_rel_insert
  :  forall D T K X
  ,  D \\- T \: K
  -> insert D X KStar \\- typ_lift X T \: K.
Proof.
  linduction T; 
  opburn'' 
    tt 
    insert_rewind 
    kind_rel 
    ltac:(fun H => match type of H with | kind => rewrite H in * end);
  match goal with
    (* TVar *)
    | [ |- context [lift_le_gt_dec ?A ?B] ] 
      => break (lift_le_gt_dec A B) ;
           econstructor ;
           opburn' (get_insert_above_idx' kind) get_insert_below_idx tt
    (* TAbs *)
    | _ 
      => econstructor; opburn' tt insert_rewind kind_rel_insert
  end.
Qed.

Theorem kind_rel_weakening
  :  forall D T K
  ,  D \\- T \: K
  -> (KStar :: D) \\- typ_lift 0 T \: K.
Proof.
  intros; rewrite K in *;
  opburn' 
    kind_rel_insert 
    cons_as_insert 
    tt.    
Qed.  

Lemma type_substition_preserves_kinding'
  :  forall (D:kenv)(X:tvar)(U T:typ)
  ,  delete D X \\- U \: KStar
  -> D \\- T \: KStar
  -> delete D X \\- [X |=> U] T \: KStar.
Proof.
  linduction T; 
  opburn' 
    kind_rel_weakening
    delete_rewind
    kind_rel;
  [ (* T-Var *)
    burn_tvar; econstructor ;
    opburn' tt (get_delete_above_idx, get_delete_below_idx) tt
  | (* T-All *)
    econstructor ;
    match goal with
    | [ H : delete ?D ?X \\- _ \: _ |- _ ] =>
      let x := fresh "D" in
      pose (x := delete D X)
    end ;
    opburn' kind_rel_weakening delete_rewind tt 
  ].
Qed.

Lemma type_substition_preserves_kinding
  :  forall (D:kenv)(X:tvar)(U T:typ)
  ,  delete (KStar :: D) 0 \\- U \: KStar
  -> (KStar :: D) \\- T \: KStar
  -> delete (KStar :: D) 0 \\- [0 |=> U] T \: KStar.
Proof. intros; eapply type_substition_preserves_kinding'; opburn. Qed.

(********************************************************************)

(* We define type environments and some operations over them here. *)
Definition tenv := list typ.
Hint Unfold tenv.

(* We will need to lift and substitute over type environments when
 * new type variables are 'pushed' *)
Definition tenv_lift (dp:nat)(G:tenv) : tenv := 
  map (typ_lift dp) G.

Definition tenv_substitute (X:tvar)(U:typ)(G:tenv) : tenv := 
  map (typ_substitute X U) G.

(********************************************************************)

Lemma delete_tenv_lift 
  :  forall G x
  ,  delete (tenv_lift 0 G) x = tenv_lift 0 (delete G x).
Proof.
  linduction x; destruct G; opburn.
Qed.

Lemma get_tenv_lift
  :  forall G x T X
  ,  get G x = Some T
  -> get (tenv_lift X G) x = Some (typ_lift X T).
Proof.
  linduction G; destruct x; opburn.
Qed.

Lemma rewind_tenv_lift
  :  forall G T X
  ,  typ_lift X T :: tenv_lift X G = tenv_lift X (T :: G).
Proof. opburn. Qed.

Lemma tenv_lift_SX
  :  forall G X
  ,  tenv_lift 0 (tenv_lift X G) = tenv_lift (S X) (tenv_lift 0 G).
Proof.
  linduction G; opburn' tt typ_lift_SX tt.
Qed.

Lemma get_tenv_substitute
  :  forall G X Y U T
  ,  get G Y = Some T
  -> get (tenv_substitute X U G) Y = Some ([X |=> U] T).
Proof.  
  linduction G; destruct Y; opburn.
Qed.

Lemma rewind_tenv_substitute
  :  forall G U T X
  ,  [X |=> U] T :: tenv_substitute X U G = tenv_substitute X U (T :: G).
Proof. opburn. Qed.

Lemma typ_lift_over_tenv_subs
  :  forall (n n':nat)(U:typ)(D:tenv)
  ,  tenv_lift n (tenv_substitute (n + n') U D) 
  =  tenv_substitute (1 + n + n') (typ_lift n U) (tenv_lift n D).
Proof.
  linduction D; 
  opburn' 
    tt 
    (typ_lift_over_subs, rewind_tenv_substitute, rewind_tenv_lift)
    tt.
Qed.

Lemma typ_lift_over_tenv_subs'
  :  forall (n n':nat)(U:typ)(D:tenv)
  ,  tenv_lift (n + n') (tenv_substitute n U D) 
  =  tenv_substitute n (typ_lift (n + n') U) (tenv_lift (1 + n + n') D).
Proof.
  linduction D; 
  opburn' 
    tt 
    (typ_lift_over_subs', rewind_tenv_substitute, rewind_tenv_lift)
    tt.
Qed.
