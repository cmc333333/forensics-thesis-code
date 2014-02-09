Require Import Coq.ZArith.ZArith.

Require Import Byte.
Require Import ByteData.
Require Import Fetch.

Definition disk_subset (sub super: Disk) :=
  forall (offset: N) (byte: Byte),
    sub offset = Found byte -> super offset = Found byte.

Infix "⊆" := disk_subset (at level 50).

Lemma subset_fmap_existence :
  forall (A: Type) (sub super: Disk) (offset: N) (fn: Byte -> A) (val: A),
    sub ⊆ super ->
    sub offset _fmap_ fn = Found val ->
    super offset _fmap_ fn = Found val.
Proof.
  intros.
  destruct (sub offset) eqn: Heq; [
    | discriminate H0
    | discriminate H0].
  apply H in Heq. rewrite <- Heq in H0. assumption.
Qed.

Lemma subset_fflatmap_existence : 
  forall (A: Type) (sub super: Disk) (offset: N) 
         (fn: Byte -> @Fetch A) (val: A),
    sub ⊆ super ->
    sub offset _fflatmap_ fn = Found val ->
    super offset _fflatmap_ fn = Found val.
Proof.
  intros.
  destruct (sub offset) eqn: Heq; [
    | discriminate H0
    | discriminate H0].
  apply H in Heq. rewrite <- Heq in H0. assumption.
Qed.

Lemma subset_shift:
  forall (amount: N) (sub super: Disk),
    sub ⊆ super ->
      (shift sub amount) ⊆ (shift super amount).
Proof.
  intros amount sub super H.
  unfold shift. unfold disk_subset.
  intros offset byte.
  apply H.
Qed.

Lemma subset_shift_found:
  forall (amount offset: N) (sub super: Disk) (val: Byte),
    sub ⊆ super ->
      (shift sub amount) offset = Found val ->
        (shift super amount) offset = Found val.
Proof.
  intros.
  apply subset_shift with (super := super) in H0; assumption.
Qed.
