(********************************************************************)
(* Tactics for rewriting *)


(********************************************************************)
(* rewrite_goal : We rewrite the current goal with any available 
 * rewrite hypothesis up to 3 variables deep. *)
Ltac rewrite_goal :=
  simpl;
  match goal with
    | [ H: eq _ _               |- _ ] => simpl; rewrite H; auto 
    | [ H: forall _,     eq _ _ |- _ ] => simpl; rewrite H; auto
    | [ H: forall _ _,   eq _ _ |- _ ] => simpl; rewrite H; auto
    | [ H: forall _ _ _, eq _ _ |- _ ] => simpl; rewrite H; auto
  end.

Ltac autorewrite_goal :=
  simpl;
  try rewrite_goal;
  autorewrite with core.