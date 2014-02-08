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


Definition fileId_subset (sub super: FileId) :=
  match (sub, super) with
  | (Ext2Id _, Ext2Id _) => sub = super
  | (MockId subData, MockId superData) =>
      forall (idx: N) (byte: Byte),
        (findInPairList subData idx) = Found byte ->
          (findInPairList superData idx) = Found byte
  | _ => False
  end.

Definition file_subset (sub super: File) :=
  fileId_subset sub.(fileId) super.(fileId)
  /\ sub.(fileSize) = super.(fileSize)
  /\ sub.(deleted) = super.(deleted)
  /\ sub.(lastAccess) = super.(lastAccess)
  /\ sub.(lastModification) = super.(lastModification)
  /\ sub.(lastCreated) = super.(lastCreated)
  /\ sub.(lastDeleted) = super.(lastDeleted).

Infix "f⊆" := file_subset (at level 50).


Definition fetchByte (fileId: FileId) (disk: Disk)
  : N->@Fetch Byte := 
  match fileId with
  | Ext2Id inodeIndex => Ext2.fileByte disk inodeIndex
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

Lemma fetchByte_subset :
  forall (file: File) (sub super: Disk) (idx: N) (byte: Byte),
    sub ⊆ super ->
      (file @[ idx | sub] = Found byte
        -> file @[ idx | super] = Found byte).
Proof.
  intros file.
  destruct file.(fileId); intros sub super idx byte subset.
    (* Ext2 *)
    simpl. apply Ext2.fileByte_subset with (1:=subset).
    (* Mock *)
    auto.
Qed.

Lemma fetchByte_fsubset :
  forall (disk: Disk) (sub super: File) (idx: N) (byte: Byte),
    sub f⊆ super ->
      (sub @[ idx | disk ] = Found byte
        -> super @[ idx | disk ] = Found byte).
Proof.
  intros disk sub super idx byte subset.
  unfold file_subset in subset. destruct subset as [Hid Heq].
  induction sub.(fileId). 
    (* Ext2 *)
    destruct super.(fileId); [ | contradict Hid ].
    rewrite Hid. auto.
    (* Mock *)
    destruct super.(fileId); [contradict Hid |].
    unfold fileId_subset in Hid.
    unfold fetchByte.
    apply Hid.
Qed.

Lemma fetchByte_subset_neg :
  forall (file: File) (sub super: Disk) (idx: N) (byte: Byte),
    sub ⊆ super ->
      (file @[- idx | sub] = Found byte
          -> file @[- idx | super] = Found byte).
Proof.
  intros file.
  destruct file.(fileId); intros sub super idx byte subset.
    (* Ext2 *)
    simpl. apply Ext2.fileByte_subset with (1:=subset).
    (* Mock *)
    auto.
Qed.

Lemma fetchByte_fsubset_neg :
  forall (disk: Disk) (sub super: File) (idx: N) (byte: Byte),
    sub f⊆ super ->
      (sub @[- idx | disk ] = Found byte
        -> super @[- idx | disk ] = Found byte).
Proof.
  intros disk sub super idx byte subset.
  unfold file_subset in subset. destruct subset as [Hid Heq].
  destruct Heq as [HfileSize Heq].
  rewrite HfileSize.
  induction sub.(fileId). 
    (* Ext2 *)
    destruct super.(fileId); [ | contradict Hid ].
    rewrite Hid. auto.
    (* Mock *)
    destruct super.(fileId); [contradict Hid |].
    unfold fileId_subset in Hid.
    simpl.
    apply Hid.
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
  destruct (fileId file) ; [| contradict H; auto].
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
  destruct file.(fileId); [| auto ].
  apply Ext2.findAndParseFile_subset with (1:=subset).
Qed.
