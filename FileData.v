Require Import Coq.ZArith.ZArith.

Require Import Byte.
Require Import ByteData.
Require Import Ext2.
Require Import Fetch.
Require Import File.
Require Import FileIds.

Local Open Scope N.

Definition findInPairList (data: list (N*Byte)) (key: N) :=
  match (find (fun pair: N*Byte => (fst pair) =? key) data) with
  | Some el => Found (snd el)
  | None => MissingAt key
  end.

Fixpoint fetchByte (fileId: FileId) (disk: Disk)
  : N->@Fetch Byte := 
  match fileId with
  | Ext2Id inodeIndex => Ext2.fileByte disk inodeIndex
  | TarId fs shiftAmt => fetchByte fs (shift disk shiftAmt)
  | MockId data => findInPairList data
  end.

(* Cleaner notation for file access. *)
Notation "f @[ i | d ]" := 
    (fetchByte f.(fileId) d i) (at level 60).
Notation "f @[- i | d ]" := 
    (fetchByte f.(fileId) d (Z.to_N ((Z.opp (Z.of_N i))
                                     mod 
                                     (Z.of_N f.(fileSize))))) 
    (at level 60).


Definition isOnDiskTry1 (file: File) (disk: Disk) :=
  exists (start: N), forall (i: N),
  i < file.(fileSize) ->
    file @[ i | disk ] = disk (start + i).

Definition isOnDisk (file: File) (disk: Disk) :=
  match file.(fileId) with
  | Ext2Id inodeIndex => 
    (Ext2.findAndParseFile disk inodeIndex) = Found file
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
