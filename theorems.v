Theorem t1 : forall (P Q : Prop), (P /\ Q) -> (Q /\ P).
intro.
intro.
intro.
destruct H.
split.
apply H0.
apply H.
Qed.

Theorem t2 : forall (P Q : Prop), (P /\ Q) <-> (Q /\ P).
intro.
intro.
split.
apply t1.
apply t1.
Qed.

Lemma imply_and_or2 : forall P Q R:Prop, (P -> Q) -> (P \/ R) -> (Q \/ R).
intro.
intro.
intro.
intro.
intro.
destruct H0.
left.
apply H.
apply H0.
right.
apply H0.
Qed.

Theorem neg_false : forall A : Prop, ~ A <-> (A <-> False).
intro.
split.
unfold not.
intro.
split.
apply H.
intro.
destruct H0.
unfold not.
intro.
destruct H.
intro.
apply H.
apply H1.
Qed.
