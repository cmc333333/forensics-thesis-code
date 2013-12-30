Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.

Open Local Scope bool.

Fixpoint string2list (str: string) :=
  match str with 
  | EmptyString => nil
  | String head tail => head :: (string2list tail)
  end.

Coercion string2list : string >-> list.

Fixpoint list2string (lst: list ascii) :=
  match lst with
  | nil => EmptyString
  | head :: tail => String head (list2string tail)
  end.


Definition ascii_eqb (lhs rhs: ascii) : bool :=
  match (lhs, rhs) with
  | (Ascii l1 l2 l3 l4 l5 l6 l7 l8, Ascii r1 r2 r3 r4 r5 r6 r7 r8) =>
      (Bool.eqb l1 r1) && (Bool.eqb l2 r2)
      && (Bool.eqb l3 r3) && (Bool.eqb l4 r4)
      && (Bool.eqb l5 r5) && (Bool.eqb l6 r6)
      && (Bool.eqb l7 r7) && (Bool.eqb l8 r8)
  end.

Lemma ascii_eqb_reflection (lhs rhs: ascii) :
  ascii_eqb lhs rhs = true <-> lhs = rhs.
Proof.
  split. (* -> *)
    intros. unfold ascii_eqb in H.
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
    intros. unfold ascii_eqb.
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

Fixpoint string_eqb (lhs rhs: string) :=
  match (lhs, rhs) with
  | (EmptyString, EmptyString) => true
  | (String l ltail, String r rtail) =>
      (ascii_eqb l r) && (string_eqb ltail rtail)
  | _ => false
  end.

Lemma string_eqb_reflection (lhs rhs: string) :
  string_eqb lhs rhs = true <-> lhs = rhs.
Proof.
  split. (* -> *)
    generalize rhs.
    induction lhs.
      destruct rhs0.
        reflexivity.
        intros. compute in H. discriminate H.
      destruct rhs0.
        intros. compute in H. discriminate H.

        intros. unfold string_eqb in H.
          apply Bool.andb_true_iff in H. destruct H.
          apply ascii_eqb_reflection in H. rewrite H; clear H.
          apply IHlhs in H0. rewrite H0; clear H0.
          reflexivity.
  (* <- *)
    generalize rhs.
    induction lhs.
      destruct rhs0.
        reflexivity.
        intros. discriminate H.
      destruct rhs0.
        intros. discriminate H.

        intros. unfold string_eqb.
          inversion H.
          apply Bool.andb_true_iff. split.
            apply ascii_eqb_reflection. reflexivity.
            rewrite <- H2 at 1. apply IHlhs in H2. auto.
Qed.
