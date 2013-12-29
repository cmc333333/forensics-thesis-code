Require Import Coq.ZArith.ZArith.

Require Import ByteData.
Require Import Fetch.
Require Import File.
Require Import FileData.

Open Local Scope bool.
Open Local Scope Z.

Definition isJpeg (file: File) (disk: Disk) :=
     file @[  0 | disk ] = Found 255
  /\ file @[  1 | disk ] = Found 216 
  /\ file @[ -2 | disk ] = Found 255
  /\ file @[ -1 | disk ] = Found 217.

Definition isJpeg_compute (file: File) (disk: Disk) :=
     Z_feqb (file @[  0 | disk ]) (Found 255)
  && Z_feqb (file @[  1 | disk ]) (Found 216)
  && Z_feqb (file @[ -2 | disk ]) (Found 255)
  && Z_feqb (file @[ -1 | disk ]) (Found 217).

Lemma isJpeg_reflection (file: File) (disk: Disk) :
  isJpeg_compute file disk = true -> isJpeg file disk.
Proof.
  intros. unfold isJpeg_compute in H. unfold isJpeg.
  apply Bool.andb_true_iff in H. destruct H.
  apply Bool.andb_true_iff in H. destruct H.
  apply Bool.andb_true_iff in H. destruct H.

  split. apply Z_feqb_reflection. auto.
  split. apply Z_feqb_reflection. auto.
  split. apply Z_feqb_reflection. auto.
  apply Z_feqb_reflection. auto.
Qed.

Definition isGzip (file: File) (disk: Disk) :=
     file @[ 0 | disk ] = Found 31
  /\ file @[ 1 | disk ] = Found 139 
  /\ file @[ 2 | disk ] = Found 8.

Definition isGzip_compute (file: File) (disk: Disk) :=
     Z_feqb (file @[ 0 | disk ]) (Found 31)
  && Z_feqb (file @[ 1 | disk ]) (Found 139)
  && Z_feqb (file @[ 2 | disk ]) (Found 8).

Lemma isGzip_reflection (file: File) (disk: Disk) :
  isGzip_compute file disk = true -> isGzip file disk.
Proof.
  intros. unfold isGzip_compute in H. unfold isGzip.
  apply Bool.andb_true_iff in H. destruct H.
  apply Bool.andb_true_iff in H. destruct H.

  split. apply Z_feqb_reflection. auto.
  split. apply Z_feqb_reflection. auto.
  apply Z_feqb_reflection. auto.
Qed.

Definition isElf (file: File) (disk: Disk) :=
     file @[ 0 | disk ] = Found 127
  /\ file @[ 1 | disk ] = Found 69 
  /\ file @[ 2 | disk ] = Found 76
  /\ file @[ 3 | disk ] = Found 70.

Definition isElf_compute (file: File) (disk: Disk) :=
     Z_feqb (file @[ 0 | disk ]) (Found 127)
  && Z_feqb (file @[ 1 | disk ]) (Found 69)
  && Z_feqb (file @[ 2 | disk ]) (Found 76)
  && Z_feqb (file @[ 3 | disk ]) (Found 70).

Lemma isElf_reflection (file: File) (disk: Disk) :
  isElf_compute file disk = true -> isElf file disk.
Proof.
  intros. unfold isElf_compute in H. unfold isElf.
  apply Bool.andb_true_iff in H. destruct H.
  apply Bool.andb_true_iff in H. destruct H.
  apply Bool.andb_true_iff in H. destruct H.

  split. apply Z_feqb_reflection. auto.
  split. apply Z_feqb_reflection. auto.
  split. apply Z_feqb_reflection. auto.
  apply Z_feqb_reflection. auto.
Qed.


Lemma jpeg_is_not_gzip : forall (file: File) (disk: Disk),
  (isJpeg file disk) -> ~ (isGzip file disk).
Proof.
  unfold isGzip, isJpeg.
  intros file disk jpeg_asmpt.
  destruct jpeg_asmpt as [byte0_is_255]. rewrite byte0_is_255.
  unfold not. intros contra. destruct contra as [not_equal].
  discriminate not_equal.
Qed.
