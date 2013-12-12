Require Import Coq.ZArith.ZArith.

Require Import ByteData.
Require Import Fetch.
Require Import File.
Require Import FileData.

Open Local Scope Z.

Definition isJpeg (file: File) (disk: Disk) :=
     file @[  0 | disk ] = Found 255
  /\ file @[  1 | disk ] = Found 216 
  /\ file @[ -2 | disk ] = Found 255
  /\ file @[ -1 | disk ] = Found 217.

Definition isGzip (file: File) (disk: Disk) :=
     file @[  0 | disk ] = Found 31
  /\ file @[  1 | disk ] = Found 139 
  /\ file @[  2 | disk ] = Found 8.

Definition isElf (file: File) (disk: Disk) :=
     file @[  0 | disk ] = Found 127
  /\ file @[  1 | disk ] = Found 69 
  /\ file @[  2 | disk ] = Found 76
  /\ file @[  3 | disk ] = Found 70.


Lemma jpeg_is_not_gzip : forall (file: File) (disk: Disk),
  (isJpeg file disk) -> ~ (isGzip file disk).
Proof.
  unfold isGzip, isJpeg.
  intros file disk jpeg_asmpt.
  destruct jpeg_asmpt as [byte0_is_255]. rewrite byte0_is_255.
  unfold not. intros contra. destruct contra as [not_equal].
  discriminate not_equal.
Qed.
