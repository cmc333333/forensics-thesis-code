Require Import Coq.ZArith.ZArith.

Require Import ByteData.
Require Import Ext2.
Require Import Fetch.
Require Import File.

Open Local Scope Z.

Definition isOnDiskTry1 (file: File) (disk: Disk) :=
  exists (start: Z), forall (i: Z),
  (i >= 0 /\ i < file.(fileSize)) ->
    file @[ i ] = disk (start + i).

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

Definition isOnDisk (file: File) (disk: Disk) :=
  (* Ext2 *)
  (exists (inodeIndex: Z),
    fileEq (Ext2.findAndParseFile disk inodeIndex)
           (Found file))
  (* Disjunction with other file systems *)
.
