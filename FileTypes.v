Require Import Coq.ZArith.ZArith.

Require Import Fetch.
Require Import File.

Open Local Scope Z.

Definition isJpeg (file: File) :=
     file @[  0 ] = Found 255
  /\ file @[  1 ] = Found 216 
  /\ file @[ -2 ] = Found 255
  /\ file @[ -1 ] = Found 217.

Definition isGzip (file: File) :=
     file @[  0 ] = Found 31
  /\ file @[  1 ] = Found 139 
  /\ file @[  2 ] = Found 8.

Definition isElf (file: File) :=
     file @[  0 ] = Found 127
  /\ file @[  1 ] = Found 69 
  /\ file @[  2 ] = Found 76
  /\ file @[  3 ] = Found 70.


Lemma jpeg_is_not_gzip : forall (file: File),
  (isJpeg file) -> ~ (isGzip file).
Proof.
  unfold isGzip, isJpeg.
  intros file jpeg_asmpt.
  destruct jpeg_asmpt as [byte0_is_255]. rewrite byte0_is_255.
  unfold not. intros contra. destruct contra as [not_equal].
  discriminate not_equal.
Qed.
