Local Open Scope bool.

Lemma reduce_prop:
  forall (P Q R :Prop),
  Q -> R -> ~P ->
    (Q \/ ~R) /\ (P \/ (~P /\ R /\ Q)).
Proof.
  intros.
  split.
    (* Q \/ ~R *)
    left. assumption.
    (* P /\ (~P /\ R /\ Q) *)
    right. 
    split.
      (* ~ P *) assumption.
    split.
      (* R *) assumption.
      (* Q *) assumption.
Qed.

Lemma reduce_bool:
  forall (p q r :bool),
  q = true -> r = true -> p = false ->
    (q || (negb r)) && (p || ((negb p) && r && q)) = true.
Proof.
  intros. rewrite H. rewrite H0. rewrite H1.
  compute.
  reflexivity.
Qed.
