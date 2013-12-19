Require Import Coq.ZArith.ZArith.

Require Import ByteData.

Inductive FileSystem: Type :=
  | Ext2FS: Z -> FileSystem
  | TarFS: FileSystem -> Z -> FileSystem
  | MockFS: ByteData -> FileSystem
.

Fixpoint eqb (lhs rhs: FileSystem) :=
  match (lhs, rhs) with
  | ((Ext2FS l), (Ext2FS r)) => Z.eqb l r
  | ((TarFS lfs l), (TarFS rfs r)) => (andb (eqb lfs rfs) (Z.eqb l r))
  | _ => false
  end.
