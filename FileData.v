Require Import Coq.ZArith.ZArith.

Require Import ByteData.
Require Import Ext2.
Require Import Fetch.
Require Import File.
Require Import FileSystems.

Open Local Scope Z.

Fixpoint fetchByteInner (fileSystem: FileSystem) (disk: Disk): Z->@Fetch Z :=
  match fileSystem with
  | Ext2FS inodeIndex => Ext2.fileByte disk inodeIndex
  | TarFS fs shiftAmt => fetchByteInner fs (shift disk shiftAmt)
  | MockFS data => data
  end.

(* Treat negative values as counting back from the end of a file 
   (a la Python) *)
Fixpoint fetchByte (file: File) (disk: Disk) (offset: Z): @Fetch Z := 
  let adjusted := if (offset <? 0) 
                  then (file.(fileSize) + offset)
                  else offset in
  (fetchByteInner file.(fileSystem)) disk adjusted.

(* Cleaner notation for file access. *)
Notation "f @[ i | d ]" := (fetchByte f d i) (at level 60).
