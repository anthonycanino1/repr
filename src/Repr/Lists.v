Require Import List.

Require Import Repr.Tactics.CpdtTactics.

Require Import Repr.Tactics.LibTactics.
Require Import Repr.Tactics.All.
Require Import Repr.Tactics.Burn.
Require Import Repr.Tactics.Rewrite.
Require Import Repr.Tactics.Opburn.


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


Lemma S_lt_length 
  :  forall X n (x:X) (ls:list X)
  ,  n < length ls -> S n < length (x :: ls).
Proof. linduction n; opburn. Qed.

Lemma length_lt_S 
  :  forall X n (x:X) (ls:list X)
  ,  S n < length (x :: ls) -> n < length ls.
Proof. opburn. Qed.

Theorem idx_lt_length 
  :  forall X idx (ls:list X)
  ,  idx < length ls 
  -> exists x, get ls idx = Some x.
Proof.
  linduction idx; destruct ls; opburn' length_lt_S tt tt; eauto.
Qed.  

Theorem get_Sidx 
  :  forall X (idx:nat) (ls:list X) (x:X)
  ,  get ls idx = get (x :: ls) (S idx).
Proof.
  linduction idx; opburn.
Qed.

Theorem get_Pidx 
  :  forall X (idx:nat) (ls:list X) (x:X)
  ,  get (x :: ls) (S idx) = get ls idx.
Proof.
  linduction idx; opburn.
Qed.

Theorem delete_rewind 
  :  forall X (idx:nat) (ls:list X) (x:X)
  ,  x :: delete ls idx = delete (x :: ls) (S idx).
Proof. opburn. Qed.

Theorem cons_as_insert
  :  forall X (ls:list X) (x:X)
  ,  x :: ls = insert ls 0 x.
Proof. linduction ls; opburn. Qed.

Theorem insert_rewind 
  :  forall X (idx:nat) (ls:list X) (x y:X)
  ,  x :: insert ls idx y = insert (x :: ls) (S idx) y.
Proof. opburn. Qed.

Lemma get_delete_above_idx' 
  :  forall X (idx n:nat) (ls:list X) r
  ,  idx < n 
  -> get ls idx            = r
  -> get (delete ls n) idx = r.
Proof.
  linduction n; destruct ls; destruct idx; destruct r;
  opburn' tt tt tt.
Qed.

Theorem get_delete_above_idx
  :  forall X (idx n:nat) (ls:list X) 
  ,  idx < n
  -> get (delete ls n) idx = get ls idx.
Proof.
  rip; break (get ls idx) as Hbk; symmetry in Hbk;
  opburn' get_delete_above_idx' tt tt.
Qed. 

Lemma get_delete_below_idx' 
  :  forall X (idx n:nat) (ls:list X) r
  ,  idx >= n 
  -> get (delete ls n) idx = r
  -> get ls (S idx)        = r.
Proof.
  linduction n; destruct ls; destruct idx; destruct r; opburn.
Qed.

Theorem get_delete_below_idx 
  :  forall X (idx n:nat) (ls:list X) 
  ,  idx >= n 
  -> get (delete ls n) idx = get ls (S idx).
Proof.
  rip; symmetry; break (get (delete ls n) idx) as Hbk;
  symmetry in Hbk; 
  opburn' get_delete_below_idx' tt tt.
Qed.

Lemma get_insert_above_idx' 
  :  forall X (idx n:nat) (ls:list X) (e:X) r
  ,  idx < n 
  -> get ls idx              = Some r
  -> get (insert ls n e) idx = Some r.
Proof.
  linduction n; destruct ls; destruct idx; opburn' tt Lt.lt_S_n tt.
Qed.

Lemma get_insert_below_idx' 
  :  forall X (idx n:nat) (ls:list X) (e:X) r
  ,  idx >= n 
  -> get ls idx                  = r
  -> get (insert ls n e) (S idx) = r.
Proof.
  linduction n; destruct ls; destruct idx; opburn. 
Qed.

Theorem get_insert_below_idx 
  :  forall X (idx n:nat) (ls:list X) (e:X)
  ,  idx >= n 
  -> get (insert ls n e) (S idx) = get ls idx.
Proof.
  rip; break (get (insert ls n e) idx); 
  opburn' get_insert_below_idx' tt tt.
Qed.

