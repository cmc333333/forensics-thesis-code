Require Import Coq.ZArith.ZArith.

Require Import Byte.
Require Import ByteData.
Require Import DiskSubset.
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
  | MockId data => findInPairList data
  | TarId fs shiftAmt => fetchByte fs (shift disk shiftAmt)
  end.

(* Cleaner notation for file access. *)
Notation "f @[ i | d ]" := 
    (fetchByte f.(fileId) d i) (at level 60).
Notation "f @[- i | d ]" := 
    (fetchByte f.(fileId) d (Z.to_N ((Z.opp (Z.of_N i))
                                     mod 
                                     (Z.of_N f.(fileSize))))) 
    (at level 60).

Lemma fetchByte_subset :
  forall (file: File) (sub super: Disk) (idx: N) (byte: Byte),
    sub ⊆ super ->
      (file @[ idx | sub] = Found byte
          -> file @[ idx | super] = Found byte)
      /\ (file @[- idx | sub] = Found byte
            -> file @[- idx | super] = Found byte).
Proof.
  intros file.
  induction file.(fileId); intros sub super idx byte subset.
    (* Ext2 *)
    split; simpl; apply Ext2.fileByte_subset with (1:=subset).
    (* Tar *)
    split; simpl; apply IHf; apply subset_shift with (1:=subset).
    (* Mock *)
    split; auto.
Qed.


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

Lemma isOnDisk_subset :
  forall (sub super: Disk) (file: File),
    sub ⊆ super ->
      isOnDisk file sub ->
        isOnDisk file super.
Proof.
  intros sub super file subset.
  unfold isOnDisk.
  destruct file.(fileId); [| auto | auto].
  apply Ext2.findAndParseFile_subset with (1:=subset).
Qed.
