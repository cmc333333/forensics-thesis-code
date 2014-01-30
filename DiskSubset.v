Require Import Coq.ZArith.ZArith.

Require Import Byte.
Require Import ByteData.
Require Import Fetch.

Definition disk_subset (sub super: Disk) :=
  forall (offset: N) (byte: Byte),
    sub offset = Found byte -> super offset = Found byte.

Infix "⊆" := disk_subset (at level 50).

Variable OriginalDisk: Disk.
