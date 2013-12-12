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
