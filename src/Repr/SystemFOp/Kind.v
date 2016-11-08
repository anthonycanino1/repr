Require Import List.
Require Import Repr.Lists.

Inductive kind : Type :=
  | KStar : kind .

Definition kenv := list kind.
Hint Unfold kenv.
