Require Import Coq.ZArith.ZArith.

Require Import ByteData.
Require Import FileSystems.

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

(*
(* Treat negative values as counting back from the end of a file 
   (a la Python) *)
Definition fetchByte (file: File) (offset: Z) (disk: Disk) := 
  if (offset <? 0)
  then (file.(data) (file.(fileSize) + offset))
  else (file.(data) offset).

(* Cleaner notation for file access. *)
Notation "d @[ i ]" := (fetchByte d i) (at level 60).


Definition fileEq (lhs rhs: @Fetch File) :=
  match (lhs, rhs) with
  | (Found lhs, Found rhs) =>
      lhs.(fileSize) = rhs.(fileSize)
      /\ lhs.(deleted) = rhs.(deleted)
      /\ forall idx:Z, lhs @[ idx ] = rhs @[ idx ]
  | (ErrorString lhs, ErrorString rhs) => lhs = rhs
  | (MissingAt lhs, MissingAt rhs) => lhs = rhs
  | _ => False
  end.
*)
