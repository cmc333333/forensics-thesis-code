Require Import Coq.ZArith.ZArith.

Require Import ByteData.
Require Import Ext2.
Require Import File.

Open Local Scope Z.

Definition isOnDiskTry1 (file: File) (disk: Disk) :=
  exists (start: Z), forall (i: Z),
  (i >= 0 /\ i < file.(fileSize)) ->
    file @[ i ] = disk (start + i).

Definition fileEq (lhs rhs: Exc File) :=
  match (lhs, rhs) with
  | (error, error) => True
  | (value lhs, value rhs) =>
      lhs.(fileSize) = rhs.(fileSize)
      /\ lhs.(deleted) = rhs.(deleted)
      /\ forall idx:Z, lhs @[ idx ] = rhs @[ idx ]
  | _ => False
  end.

Definition isOnDisk (file: File) (disk: Disk) :=
  (* Ext2 *)
  (exists (inodeIndex: Z),
    fileEq (Ext2.findAndParseFile disk inodeIndex)
           (value file))
  (* Disjunction with other file systems *)
.
