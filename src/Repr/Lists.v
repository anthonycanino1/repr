Require Import List.

Require Import Repr.Tactics.CpdtTactics.

Require Import Repr.Tactics.LibTactics.
Require Import Repr.Tactics.All.
Require Import Repr.Tactics.Burn.
Require Import Repr.Tactics.Rewrite.


(********************************************************************)
(* Definitions *)

Fixpoint get (X:Type) (ls:list X) (idx:nat) : option X :=
  match ls, idx with
    | l :: ls', O      => Some l
    | l :: ls', S idx' => get _ ls' idx'
    | _, _             => None
  end.

Arguments get [X] _ _.

Fixpoint delete (X:Type) (ls:list X) (idx:nat) : list X :=
  match ls, idx with
    | l :: ls', O      => ls'
    | l :: ls', S idx' => l :: delete _ ls' idx'
    | nil, _           => nil
  end.

Arguments delete [X] ls idx.

Fixpoint insert (X:Type) (ls:list X) (idx:nat) (elm:X) : list X :=
  match ls, idx with
    | nil, _           => elm :: nil
    | _, O             => elm :: ls 
    | l :: ls', S idx' => l :: insert _ ls' idx' elm
  end.

Arguments insert [X] _ _ _.

Fixpoint get_split (X:Type) (ls:list X) (idx:nat) : option (X * list X * list X) :=
  match ls, idx with
    | l :: ls', O      => Some (l,nil,ls')
    | l :: ls', S idx' => 
       match (get_split _ ls' idx')  with
         | Some (x, lls, rls) 
           => Some (x, l :: lls, rls)
         | None          
           => None
       end
    | _, _             => None
  end.

Arguments get_split [X] _ _.

(********************************************************************)
(* Lemmas *)

Lemma S_lt_length :
  forall X n (x:X) (ls:list X), n < length ls -> S n < length (x :: ls).
Proof. induction n; burn. Qed.

Lemma length_lt_S :
 forall X n (x:X) (ls:list X), S n < length (x :: ls) -> n < length ls.
Proof. crush. Qed.

Theorem idx_lt_length : 
  forall X idx (ls:list X), idx < length ls -> exists x, get ls idx = Some x.
Proof.
  induction idx; introh Hlt; destruct ls; simpl; clean 1.
  eexists; trivial.
  apply length_lt_S in Hlt; specialize (IHidx _ Hlt); elim IHidx; intros; rewrite H;
   eexists; reflexivity.
Qed.  

Theorem get_Sidx :
  forall X (idx:nat) (ls:list X) (x:X), get ls idx = get (x :: ls) (S idx).
Proof.
  rip; gen ls x; induction idx; burn.
Qed.

Theorem get_Pidx :
  forall X (idx:nat) (ls:list X) (x:X), get (x :: ls) (S idx) = get ls idx.
Proof.
  rip; gen ls x; induction idx; burn.
Qed.

Theorem delete_rewind :
  forall X (idx:nat) (ls:list X) (x:X), x :: delete ls idx = delete (x :: ls) (S idx).
Proof. crush. Qed.

Lemma get_delete_above_idx' 
  :  forall X (idx n:nat) (ls:list X) r
  ,  idx < n 
  -> get ls idx            = r
  -> get (delete ls n) idx = r.
Proof.
  rip; gen idx ls; induction n; destruct ls; destruct idx; tburn.
  rip; apply IHn; burn.
Qed.
Hint Resolve get_delete_above_idx'.

Theorem get_delete_above_idx
  :  forall X (idx n:nat) (ls:list X) 
  ,  idx < n
  -> get (delete ls n) idx = get ls idx.
Proof.
  rip; break (get ls idx); burn.
Qed. 
Hint Rewrite get_delete_above_idx. 

Lemma get_delete_below_idx' 
  :  forall X (idx n:nat) (ls:list X) r
  ,  idx >= n 
  -> get (delete ls n) idx = r
  -> get ls (S idx)        = r.
Proof.
  rip; gen idx ls; induction n; rip; break ls; break idx; subst; tburn.
  simpl; simpl in *; apply IHn; burn.
Qed.
Hint Resolve get_delete_below_idx'.

Theorem get_delete_below_idx 
  :  forall X (idx n:nat) (ls:list X) 
  ,  idx >= n 
  -> get (delete ls n) idx = get ls (S idx).
Proof.
  rip; break (get (delete ls n) idx); symmetry; burn.
Qed.
Hint Rewrite get_delete_below_idx.

Theorem insert_rewind 
  :  forall X (idx:nat) (ls:list X) (x y:X)
  ,  x :: insert ls idx y = insert (x :: ls) (S idx) y.
Proof. crush. Qed.

Lemma get_insert_above_idx' 
  :  forall X (idx n:nat) (ls:list X) (e:X) r
  ,  idx < n 
  -> get ls idx              = Some r
  -> get (insert ls n e) idx = Some r.
Proof.
  rip; gen idx ls e r; induction n; destruct ls; destruct idx; tburn.
  rip; apply IHn; burn.
Qed.
Hint Resolve get_insert_above_idx'.

(*
Theorem get_insert_above_idx
  :  forall X (idx n:nat) (ls:list X) (e:X)
  ,  idx < n
  -> get (insert ls n e) idx = get ls idx.
Proof.
  rip; break (get ls idx). eapply get_insert_above_idx'; burn. 
Qed. 
Hint Rewrite get_delete_above_idx. *)

Lemma get_insert_below_idx' 
  :  forall X (idx n:nat) (ls:list X) (e:X) r
  ,  idx >= n 
  -> get ls idx                  = r
  -> get (insert ls n e) (S idx) = r.
Proof.
  rip; gen idx ls e; induction n; rip; break ls; break idx; subst; tburn.
  simpl; simpl in *; apply IHn; burn.
Qed.
Hint Resolve get_insert_below_idx'.

Theorem get_insert_below_idx 
  :  forall X (idx n:nat) (ls:list X) (e:X)
  ,  idx >= n 
  -> get (insert ls n e) (S idx) = get ls idx.
Proof.
  rip; break (get (insert ls n e) idx); burn.
Qed.
Hint Rewrite get_insert_below_idx.

  


  








  

  
  

