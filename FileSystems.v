Require Import Coq.ZArith.ZArith.

Require Import ByteData.

Inductive FileSystem: Type :=
  | Ext2FS: Z -> FileSystem
  | TarFS: FileSystem -> Z -> FileSystem
  | MockFS: ByteData -> FileSystem
.

(*
Require Import ByteData.
Require Import Ext2.
Require Import Fetch.
Require Import File.

Open Local Scope Z.

Definition isOnDiskTry1 (file: File) (disk: Disk) :=
  exists (start: Z), forall (i: Z),
  (i >= 0 /\ i < file.(fileSize)) ->
    file @[ i ] = disk (start + i).

Definition isOnDisk (file: File) (disk: Disk) :=
  (* Ext2 *)
  (exists (inodeIndex: Z),
    fileEq (Ext2.findAndParseFile disk inodeIndex)
           (Found file))
  (* Disjunction with other file systems *)
.
*)
