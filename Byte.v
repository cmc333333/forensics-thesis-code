Require Import Coq.Strings.Ascii.
Require Import Coq.ZArith.ZArith.

Require Import Fetch.

Definition Byte := ascii.

Local Open Scope bool.

Definition eqb (lhs rhs: Byte) : bool :=
  match (lhs, rhs) with
  | (Ascii l1 l2 l3 l4 l5 l6 l7 l8, Ascii r1 r2 r3 r4 r5 r6 r7 r8) =>
      (Bool.eqb l1 r1) && (Bool.eqb l2 r2)
      && (Bool.eqb l3 r3) && (Bool.eqb l4 r4)
      && (Bool.eqb l5 r5) && (Bool.eqb l6 r6)
      && (Bool.eqb l7 r7) && (Bool.eqb l8 r8)
  end.

Lemma eqb_reflection (lhs rhs: Byte) :
  eqb lhs rhs = true <-> lhs = rhs.
Proof.
  split. (* -> *)
    intros. unfold eqb in H.
    destruct lhs. destruct rhs.
    apply Bool.andb_true_iff in H. destruct H. 
    apply Bool.andb_true_iff in H. destruct H. 
    apply Bool.andb_true_iff in H. destruct H. 
    apply Bool.andb_true_iff in H. destruct H. 
    apply Bool.andb_true_iff in H. destruct H. 
    apply Bool.andb_true_iff in H. destruct H. 
    apply Bool.andb_true_iff in H. destruct H. 
    apply Bool.eqb_prop in H; rewrite H; clear H.
    apply Bool.eqb_prop in H0; rewrite H0; clear H0.
    apply Bool.eqb_prop in H1; rewrite H1; clear H1.
    apply Bool.eqb_prop in H2; rewrite H2; clear H2.
    apply Bool.eqb_prop in H3; rewrite H3; clear H3.
    apply Bool.eqb_prop in H4; rewrite H4; clear H4.
    apply Bool.eqb_prop in H5; rewrite H5; clear H5.
    apply Bool.eqb_prop in H6; rewrite H6; clear H6.
    reflexivity.
  (* <- *)
    intros. unfold eqb.
    destruct lhs. destruct rhs. inversion H. 
    apply Bool.andb_true_iff. split; [| apply Bool.eqb_reflx].
    apply Bool.andb_true_iff. split; [| apply Bool.eqb_reflx].
    apply Bool.andb_true_iff. split; [| apply Bool.eqb_reflx].
    apply Bool.andb_true_iff. split; [| apply Bool.eqb_reflx].
    apply Bool.andb_true_iff. split; [| apply Bool.eqb_reflx].
    apply Bool.andb_true_iff. split; [| apply Bool.eqb_reflx].
    apply Bool.andb_true_iff. split; [| apply Bool.eqb_reflx].
    apply Bool.eqb_reflx.
Qed.


Definition feqb (lhs rhs: @Fetch Byte) := Fetch.eqb lhs rhs eqb.

Lemma feqb_reflection (lhs rhs: @Fetch Byte):
  feqb lhs rhs = true -> lhs = rhs.
Proof.
  intros. unfold feqb in H. unfold eqb in H.
  destruct lhs.
    destruct rhs; [| discriminate H | discriminate H]. 
      apply eqb_reflection in H. rewrite H. reflexivity.
    destruct rhs; [discriminate H | | discriminate H].
      apply N.eqb_eq in H. rewrite H. reflexivity.
    discriminate H.
Qed.
