Require Import List.
Require Import Repr.Lists.

Inductive kind : Set :=
  | KStar : kind .

Definition kenv := list kind.
Hint Unfold kenv.
