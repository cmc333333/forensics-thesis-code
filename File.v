Require Import Coq.ZArith.ZArith.

Require Import ByteData.

Open Local Scope Z.

Structure File := mkFile {
  fileSystemId: Exc Z;
  fileSize: Z;
  deleted: bool;
  data: ByteData;
  lastAccess: Exc Z;
  lastModification: Exc Z;
  lastCreated: Exc Z;
  lastDeleted: Exc Z
}.


(* Treat negative values as counting back from the end of a file 
   (a la Python) *)
Definition fetchByte (file: File) (offset: Z) := if (offset <? 0)
  then (file.(data) (file.(fileSize) + offset))
  else (file.(data) offset).

(* Cleaner notation for file access. *)
Notation "d @[ i ]" := (fetchByte d i) (at level 60).

Definition isDeleted (file: File) := 
  file.(deleted) = true.
