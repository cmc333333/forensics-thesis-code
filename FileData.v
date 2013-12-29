Require Import Coq.ZArith.ZArith.

Require Import ByteData.
Require Import Ext2.
Require Import Fetch.
Require Import File.
Require Import FileIds.

Open Local Scope Z.

Fixpoint fetchByteInner (fileId: FileId) (disk: Disk): Z->@Fetch Z :=
  match fileId with
  | Ext2Id inodeIndex => Ext2.fileByte disk inodeIndex
  | TarId fs shiftAmt => fetchByteInner fs (shift disk shiftAmt)
  | MockId data => data
  end.

(* Treat negative values as counting back from the end of a file 
   (a la Python) *)
Fixpoint fetchByte (file: File) (disk: Disk) (offset: Z): @Fetch Z := 
  let adjusted := if (offset <? 0) 
                  then (file.(fileSize) + offset)
                  else offset in
  (fetchByteInner file.(fileId)) disk adjusted.

(* Cleaner notation for file access. *)
Notation "f @[ i | d ]" := (fetchByte f d i) (at level 60).



Definition isOnDiskTry1 (file: File) (disk: Disk) :=
  exists (start: Z), forall (i: Z),
  (i >= 0 /\ i < file.(fileSize)) ->
    file @[ i | disk ] = disk (start + i).

Definition isOnDisk (file: File) (disk: Disk) :=
  match file.(fileId) with
  | Ext2Id inodeIndex => (Ext2.findAndParseFile disk inodeIndex) = Found file
  | _ => False
  end.

Definition isOnDisk_compute (file: File) (disk: Disk) :=
  match file.(fileId) with
  | Ext2Id inodeIndex => File.feqb (Ext2.findAndParseFile disk inodeIndex)
                                  (Found file)
  | _ => false
  end.

Lemma isOnDisk_reflection (file: File) (disk: Disk) :
  (isOnDisk_compute file disk) = true -> (isOnDisk file disk).
Proof.
  intros.
  unfold isOnDisk_compute in H. unfold isOnDisk.
  destruct (fileId file) ; [ | contradict H; auto | contradict H; auto].
  apply feqb_reflection. auto.
Qed.
