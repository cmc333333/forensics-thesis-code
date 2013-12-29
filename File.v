Require Import Coq.ZArith.ZArith.

Require Import ByteData.
Require Import Fetch.
Require Import FileSystems.
Require Import Util.

Open Local Scope bool.
Open Local Scope Z.

Structure File := mkFile {
  fileSystem: FileSystem;
  fileSize: Z;
  deleted: bool;
  lastAccess: Exc Z;
  lastModification: Exc Z;
  lastCreated: Exc Z;
  lastDeleted: Exc Z
}.

Definition isDeleted (file: File) := 
  file.(deleted) = true.

Definition eqb (lhs rhs: File) :=
  (FileSystems.eqb lhs.(fileSystem) rhs.(fileSystem))
  && (lhs.(fileSize) =? rhs.(fileSize))
  && (Bool.eqb lhs.(deleted) rhs.(deleted))
  && (optZ_eqb lhs.(lastAccess) rhs.(lastAccess))
  && (optZ_eqb lhs.(lastModification) rhs.(lastModification))
  && (optZ_eqb lhs.(lastCreated) rhs.(lastCreated))
  && (optZ_eqb lhs.(lastDeleted) rhs.(lastDeleted)).

Lemma eqb_reflection (lhs rhs: File):
  eqb lhs rhs = true -> lhs = rhs.
Proof.
  intros. unfold eqb in H.
  apply Bool.andb_true_iff in H. destruct H.
  apply Bool.andb_true_iff in H. destruct H.
  apply Bool.andb_true_iff in H. destruct H.
  apply Bool.andb_true_iff in H. destruct H.
  apply Bool.andb_true_iff in H. destruct H.
  apply Bool.andb_true_iff in H. destruct H.

  destruct lhs. destruct rhs. 
  simpl in H, H0, H1, H2, H3, H4, H5.
  apply eqb_reflection in H. rewrite H. clear H.
  apply Z.eqb_eq in H5. rewrite H5. clear H5.
  apply -> Bool.eqb_true_iff in H4. rewrite H4. clear H4.
  apply optZ_eqb_reflection in H0. rewrite H0. clear H0.
  apply optZ_eqb_reflection in H1. rewrite H1. clear H1.
  apply optZ_eqb_reflection in H2. rewrite H2. clear H2.
  apply optZ_eqb_reflection in H3. rewrite H3. clear H3.
  reflexivity.
Qed.

Definition feqb (lhs rhs: @Fetch File) := Fetch.eqb lhs rhs eqb.

Lemma feqb_reflection (lhs rhs: @Fetch File) :
  feqb lhs rhs = true -> lhs = rhs.
Proof.
  intros.
  unfold feqb in H. unfold Fetch.eqb in H.
  destruct lhs. 
    destruct rhs ; [| discriminate H | discriminate H].
      apply eqb_reflection in H. rewrite H. reflexivity.
    destruct rhs ; [discriminate H | | discriminate H].
      apply Z.eqb_eq in H. rewrite H. reflexivity.
    destruct rhs ; [discriminate H | discriminate H |].
      discriminate H.
Qed.
