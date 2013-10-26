Require Import Coq.ZArith.ZArith.

Require Import File.

Open Local Scope Z.

Definition isJpeg (file: File) :=
     file @[  0 ] = value 255
  /\ file @[  1 ] = value 216 
  /\ file @[ -2 ] = value 255
  /\ file @[ -1 ] = value 217.

Definition isGzip (file: File) :=
     file @[  0 ] = value 31
  /\ file @[  1 ] = value 139 
  /\ file @[  2 ] = value 8.

Definition isElf (file: File) :=
     file @[  0 ] = value 127
  /\ file @[  1 ] = value 69 
  /\ file @[  2 ] = value 76
  /\ file @[  3 ] = value 70.


Lemma jpeg_is_not_gzip : forall (file: File),
  (isJpeg file) -> ~ (isGzip file).
Proof.
  unfold isGzip, isJpeg.
  intros file jpeg_asmpt.
  destruct jpeg_asmpt as [byte0_is_255]. rewrite byte0_is_255.
  unfold not. intros contra. destruct contra as [not_equal].
  discriminate not_equal.
Qed.
