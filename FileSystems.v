Require Import Coq.ZArith.ZArith.

Require Import ByteData.

Inductive FileSystem: Type :=
  | Ext2FS: Z -> FileSystem
  | TarFS: FileSystem -> Z -> FileSystem
  | MockFS: ByteData -> FileSystem
.
