Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Require Import Byte.
Require Import ByteData.
Require Import DiskSubset.
Require Import Fetch.
Require Import File.
Require Import StringOps.
Require Import Util.

Local Open Scope N.

(* Field names based on http://www.nongnu.org/ext2-doc/ext2.html *)

(* Block Address will come up again and again *)
Definition BA := N.


(* ======= SuperBlock ======= *)
Structure SuperBlock := mkSuperBlock {
  inodesCount: N;
  blocksCount: N;
  rBlocksCount: N;
  freeBlocksCount: N;
  freeInodesCount: N;
  firstDataBlock: BA;
  logBlockSize: N;
  logFragSize: N;
  blocksPerGroup: N;
  fragsPerGroup: N;
  inodesPerGroup: N;
  mTime: N;
  wTime: N;
  mntCount: N;
  maxMntCount: N;
  magic: N;
  state: N;
  errors: N;
  minorRevLevel: N;
  lastCheck: N;
  checkinterval: N;
  creatorOS: N;
  revLevel: N;
  defResuid: N;
  defResgid: N;
  (* EXT2_DYNAMIC_REV Specific *)
  firstIno: N;
  inodeSize: N;
  blockGroupNr: N;
  featureCompat: N;
  featureIncompat: N;
  featureROCompat: N;
  uuid: list Byte;
  volumeName: string;
  lastMounted: string;
  algoBitmap: N;
  (* Performance Hints *)
  preallocBlocks: N;
  preallocDirBlocks: N;
  (* Journaling Support *)
  journalUUID: N;
  journalInum: N;
  journalDev: N;
  lastOrphan: N;
  (* Directory Indexing Support *)
  hashSeed: N;
  defHashVersion: N;
  (* Other options *)
  defaultMountOptions: N;
  firstMetaBg: N
}.

Definition findAndParseSuperBlock (disk: Disk)
  : @Fetch SuperBlock :=
  let disk := (shift disk 1024) in
  (seq_lendu disk 0 4) _fflatmap_ (fun inodesCount =>
  (seq_lendu disk 4 4) _fflatmap_ (fun blocksCount =>
  (seq_lendu disk 8 4) _fflatmap_ (fun rBlocksCount =>
  (seq_lendu disk 12 4) _fflatmap_ (fun freeBlocksCount =>
  (seq_lendu disk 16 4) _fflatmap_ (fun freeInodesCount =>
  (seq_lendu disk 20 4) _fflatmap_ (fun firstDataBlock =>
  (seq_lendu disk 24 4) _fflatmap_ (fun logBlockSize =>
  (seq_lendu disk 28 4) _fflatmap_ (fun logFragSize =>
  (seq_lendu disk 32 4) _fflatmap_ (fun blocksPerGroup =>
  (seq_lendu disk 36 4) _fflatmap_ (fun fragsPerGroup =>
  (seq_lendu disk 40 4) _fflatmap_ (fun inodesPerGroup =>
  (seq_lendu disk 44 4) _fflatmap_ (fun mTime =>
  (seq_lendu disk 48 4) _fflatmap_ (fun wTime =>
  (seq_lendu disk 52 2) _fflatmap_ (fun mntCount =>
  (seq_lendu disk 54 2) _fflatmap_ (fun maxMntCount =>
  (seq_lendu disk 56 2) _fflatmap_ (fun magic =>
  (seq_lendu disk 58 2) _fflatmap_ (fun state =>
  (seq_lendu disk 60 2) _fflatmap_ (fun errors =>
  (seq_lendu disk 62 2) _fflatmap_ (fun minorRevLevel =>
  (seq_lendu disk 64 4) _fflatmap_ (fun lastCheck =>
  (seq_lendu disk 68 4) _fflatmap_ (fun checkinterval =>
  (seq_lendu disk 72 4) _fflatmap_ (fun creatorOS =>
  (seq_lendu disk 76 4) _fflatmap_ (fun revLevel =>
  (seq_lendu disk 80 2) _fflatmap_ (fun defResuid =>
  (seq_lendu disk 82 2) _fflatmap_ (fun defResgid =>
  (seq_lendu disk 84 4) _fflatmap_ (fun firstIno =>
  (seq_lendu disk 88 2) _fflatmap_ (fun inodeSize =>
  (seq_lendu disk 90 2) _fflatmap_ (fun blockGroupNr =>
  (seq_lendu disk 92 4) _fflatmap_ (fun featureCompat =>
  (seq_lendu disk 96 4) _fflatmap_ (fun featureIncompat =>
  (seq_lendu disk 100 4) _fflatmap_ (fun featureROCompat =>
  (seq_list disk 104 16) _fflatmap_ (fun uuid =>
  (seq_list disk 120 16) _fflatmap_ (fun volumeName =>
  (seq_list disk 136 64) _fflatmap_ (fun lastMounted =>
  (seq_lendu disk 200 4) _fflatmap_ (fun algoBitmap =>
  (disk 204) _fflatmap_ (fun preallocBlocks =>
  (disk 205) _fflatmap_ (fun preallocDirBlocks =>
  (seq_lendu disk 208 16) _fflatmap_ (fun journalUUID =>
  (seq_lendu disk 224 4) _fflatmap_ (fun journalInum =>
  (seq_lendu disk 228 4) _fflatmap_ (fun journalDev =>
  (seq_lendu disk 232 4) _fflatmap_ (fun lastOrphan =>
  (seq_lendu disk 236 16) _fflatmap_ (fun hashSeed =>
  (disk 252) _fflatmap_ (fun defHashVersion =>
  (seq_lendu disk 256 4) _fflatmap_ (fun defaultMountOptions =>
  (seq_lendu disk 260 4) _fmap_ (fun firstMetaBg =>
    mkSuperBlock
      inodesCount
      blocksCount
      rBlocksCount
      freeBlocksCount
      freeInodesCount
      firstDataBlock
      logBlockSize
      logFragSize
      blocksPerGroup
      fragsPerGroup
      inodesPerGroup
      mTime
      wTime
      mntCount
      maxMntCount
      magic
      state
      errors
      minorRevLevel
      lastCheck
      checkinterval
      creatorOS
      revLevel
      defResuid
      defResgid
      firstIno
      inodeSize
      blockGroupNr
      featureCompat
      featureIncompat
      featureROCompat
      uuid
      (list2string volumeName)
      (list2string lastMounted)
      algoBitmap
      (N_of_ascii preallocBlocks)
      (N_of_ascii preallocDirBlocks)
      journalUUID
      journalInum
      journalDev
      lastOrphan
      hashSeed
      (N_of_ascii defHashVersion)
      defaultMountOptions
      firstMetaBg
  ))))))))))))))))))))))))))))))))))))))))))))).


Lemma findAndParseSuperBlock_subset :
  forall (sub super:Disk) (superblock: SuperBlock),
    sub ⊆ super ->
      findAndParseSuperBlock sub = Found superblock ->
        findAndParseSuperBlock super = Found superblock.
Proof.
  intros sub super superblock subset.
  unfold findAndParseSuperBlock.
  unfold disk_subset in subset.
  repeat (apply found_fflatmap_found_twice; [
    intros ?;
    try solve [
      apply seq_lendu_shift_subset with (1:=subset)
      || apply seq_list_shift_subset with (1:=subset)
      || apply subset_shift_found with (1:=subset) ] 
    | intro; intro ]). 
  intros. assumption.
Qed.

Definition blockSize (superblock: SuperBlock) :=
  N.shiftl 1024 superblock.(logBlockSize).

Definition ba2Offset (superblock: SuperBlock) (blockAddress: BA)
  := (blockSize superblock) * blockAddress.


(* ======= GroupDescriptor ======= *)
Structure GroupDescriptor := mkGroupDescriptor {
  blockBitmap: BA;
  inodeBitmap: BA;
  inodeTable: BA;
  gdFreeBlocksCount: N;
  gdFreeInodesCount: N;
  usedDirsCount: N
}.

Definition findAndParseGroupDescriptor 
  (disk: Disk) (superblock: SuperBlock) (groupId: N)
  : @Fetch GroupDescriptor :=
  let groupBlockArrayBA := if (1024 <? blockSize superblock)
    then 1 else 2 in
  let groupBlockArrayOffset :=
    ba2Offset superblock groupBlockArrayBA in
  let descriptorOffset := 32 * groupId in
  let disk := (shift disk (groupBlockArrayOffset
                           + descriptorOffset)) in
  (seq_lendu disk 0 4) _fflatmap_ (fun blockBitmap =>
  (seq_lendu disk 4 4) _fflatmap_ (fun inodeBitmap =>
  (seq_lendu disk 8 4) _fflatmap_ (fun inodeTable =>
  (seq_lendu disk 12 2) _fflatmap_ (fun gdFreeBlocksCount =>
  (seq_lendu disk 14 2) _fflatmap_ (fun gdFreeInodesCount =>
  (seq_lendu disk 16 2) _fmap_ (fun usedDirsCount =>
    mkGroupDescriptor
      blockBitmap
      inodeBitmap
      inodeTable
      gdFreeBlocksCount
      gdFreeInodesCount
      usedDirsCount
  )))))).

Lemma findAndParseGroupDescriptor_subset :
  forall (sub super:Disk) (sb: SuperBlock) (groupId: N)
         (groupDesc: GroupDescriptor),
    sub ⊆ super ->
      findAndParseGroupDescriptor sub sb groupId = Found groupDesc ->
        findAndParseGroupDescriptor super sb groupId = Found groupDesc.
Proof.
  intros sub super sb groupId groupDesc subset.
  unfold findAndParseGroupDescriptor.
  unfold disk_subset in subset.
  repeat (apply found_fflatmap_found_twice; [
    intros ?;
    try solve [
      apply seq_lendu_shift_subset with (1:=subset)
      || apply seq_list_shift_subset with (1:=subset)
      || apply subset_shift_found with (1:=subset) ] 
    | intro; intro ]). 
  intros. assumption.
Qed.


(* ======= INode ======= *)
Structure Inode := mkInode {
  mode: N;
  uid: N;
  size: N;
  atime: N;
  ctime: N;
  mtime: N;
  dtime: N;
  gid: N;
  linksCount: N;
  blocks: N;
  flags: N;
  osd1: N;
  block: list BA;
  generation: N;
  fileACL: N;
  dirACL: N;
  faddr: N;
  osd2: N
}.

Definition findAndParseInode (disk: Disk)
  (superblock: SuperBlock) (groupdesc: GroupDescriptor)
  (inodeIndex: N): @Fetch Inode :=
  (* Check for valid Inode *)
  if (superblock.(inodesCount) <=? inodeIndex)
  then ErrorString "Invalid inode index"
  else
    (* Inode Table is 1-indexed *)
    let inodeIndexInTable := 
      ((inodeIndex - 1) mod superblock.(inodesPerGroup)) in
    let inodePos := (ba2Offset superblock
                               groupdesc.(inodeTable))
                     + (inodeIndexInTable * 128) in
    let disk := (shift disk inodePos) in
    (seq_lendu disk 0 2) _fflatmap_ (fun mode =>
    (seq_lendu disk 2 2) _fflatmap_ (fun uid =>
    (seq_lendu disk 4 4) _fflatmap_ (fun size =>
    (seq_lendu disk 8 4) _fflatmap_ (fun atime =>
    (seq_lendu disk 12 4) _fflatmap_ (fun ctime =>
    (seq_lendu disk 16 4) _fflatmap_ (fun mtime =>
    (seq_lendu disk 20 4) _fflatmap_ (fun dtime =>
    (seq_lendu disk 24 2) _fflatmap_ (fun gid =>
    (seq_lendu disk 26 2) _fflatmap_ (fun linksCount =>
    (seq_lendu disk 28 4) _fflatmap_ (fun blocks =>
    (seq_lendu disk 32 4) _fflatmap_ (fun flags =>
    (seq_lendu disk 36 4) _fflatmap_ (fun osd1 =>
    (seq_lendu disk 40 4) _fflatmap_ (fun directBlock1 =>
    (seq_lendu disk 44 4) _fflatmap_ (fun directBlock2 =>
    (seq_lendu disk 48 4) _fflatmap_ (fun directBlock3 =>
    (seq_lendu disk 52 4) _fflatmap_ (fun directBlock4 =>
    (seq_lendu disk 56 4) _fflatmap_ (fun directBlock5 =>
    (seq_lendu disk 60 4) _fflatmap_ (fun directBlock6 =>
    (seq_lendu disk 64 4) _fflatmap_ (fun directBlock7 =>
    (seq_lendu disk 68 4) _fflatmap_ (fun directBlock8 =>
    (seq_lendu disk 72 4) _fflatmap_ (fun directBlock9 =>
    (seq_lendu disk 76 4) _fflatmap_ (fun directBlock10 =>
    (seq_lendu disk 80 4) _fflatmap_ (fun directBlock11 =>
    (seq_lendu disk 84 4) _fflatmap_ (fun directBlock12 =>
    (seq_lendu disk 88 4) _fflatmap_ (fun indirectBlock =>
    (seq_lendu disk 92 4) _fflatmap_ (fun 
                                      doubleIndirectBlock =>
    (seq_lendu disk 96 4) _fflatmap_ (fun 
                                      tripleIndirectBlock =>
    (seq_lendu disk 100 4) _fflatmap_ (fun generation =>
    (seq_lendu disk 104 4) _fflatmap_ (fun fileACL =>
    (seq_lendu disk 108 4) _fflatmap_ (fun dirACL =>
    (seq_lendu disk 112 4) _fflatmap_ (fun faddr =>
    (seq_lendu disk 116 4) _fmap_ (fun osd2 =>
      mkInode
        mode
        uid
        size
        atime
        ctime
        mtime
        dtime
        gid
        linksCount
        blocks
        flags
        osd1
        (directBlock1 :: directBlock2 :: directBlock3
          :: directBlock4 :: directBlock5 :: directBlock6
          :: directBlock7 :: directBlock8 :: directBlock9
          :: directBlock10 :: directBlock11 :: directBlock12
          :: indirectBlock :: doubleIndirectBlock
          :: tripleIndirectBlock :: nil)
        generation
        fileACL
        dirACL
        faddr
        osd2
  )))))))))))))))))))))))))))))))).

Lemma findAndParseInode_subset :
  forall (sub super:Disk) (sb: SuperBlock) (gd: GroupDescriptor)
         (inodeIndex: N) (inode: Inode),
    sub ⊆ super ->
      findAndParseInode sub sb gd inodeIndex = Found inode ->
        findAndParseInode super sb gd inodeIndex = Found inode.
Proof.
  intros sub super sb gd inodeIndex inode subset.
  unfold findAndParseInode.
  unfold disk_subset in subset.
  destruct (inodesCount sb <=? inodeIndex); [ auto|].
  repeat (apply found_fflatmap_found_twice; [
    intros ?;
    try solve [
      apply seq_lendu_shift_subset with (1:=subset)
      || apply seq_list_shift_subset with (1:=subset)
      || apply subset_shift_found with (1:=subset) ] 
    | intro; intro ]). 
  intros. assumption.
Qed.


(* ======= Fetch Arbitrary Bytes For An Inode ======= *)
(* Recursive function for dealing with levels of indirection *)
Fixpoint walkIndirection (disk: Disk) (superblock: SuperBlock)
  (blockNumber indirectionPos: N) (indirectionLevel: nat) 
  : @Fetch BA :=
  match indirectionLevel with
  | O => 
    let bytePosition := (indirectionPos + 4 * blockNumber) in
    (seq_lendu disk bytePosition 4)
  | S nextIndirectionLevel =>
    (* Type conversion *)
    let exponent := N.of_nat indirectionLevel in
    let unitSizeInBlocks := 
      ((blockSize superblock) ^ exponent) / (4 ^ exponent) in
    let nextBlockIndex := blockNumber / unitSizeInBlocks in
    let nextBytePosition := 
      indirectionPos + 4 * nextBlockIndex in
    (seq_lendu disk nextBytePosition 4) 
      _fflatmap_ (fun nextBlockBA =>
      walkIndirection disk superblock 
                      (blockNumber mod unitSizeInBlocks)
                      (ba2Offset superblock nextBlockBA)
                      nextIndirectionLevel
    )
  end.

Lemma walkIndirection_subset :
  forall (sub super:Disk) (sb: SuperBlock) (blockNum indPos: N)
         (indLevel: nat) (ba: BA),
    sub ⊆ super ->
      walkIndirection sub sb blockNum indPos indLevel = Found ba ->
        walkIndirection super sb blockNum indPos indLevel = Found ba.
Proof.
  intros sub super sb blockNum indPos indLevel ba subset.
  generalize blockNum indPos. clear blockNum indPos.
  induction indLevel.
  (* Zero Case *)
  intros blockNum indPos.
  unfold walkIndirection. apply seq_lendu_subset with (1:=subset).
  (* Inductive Case *)
  (* Unfold one level *)
  intros blockNum indPos.
  unfold walkIndirection. fold walkIndirection.
  intros subH. 
  apply found_fflatmap_found in subH.
  destruct subH as [aval [Haval subH]].
  apply seq_lendu_subset with (1:=subset) in Haval.
  rewrite Haval.
  unfold fetch_flatmap.
  apply IHindLevel. assumption.
Qed.


Definition fetchInodeByte (disk: Disk) (superblock: SuperBlock) 
  (inode: Inode) (bytePos: N): @Fetch Byte :=
  if inode.(size) <=? bytePos then 
    MissingAt bytePos
  else 
    let blockSize := (blockSize superblock) in
    let blockNumInFile := bytePos / blockSize in
    let directAddressable := 12 in
    let indirect1Addressable := blockSize / 4 in
    let indirect2Addressable := (blockSize * blockSize) / 16 in

    (if blockNumInFile <=? directAddressable then
      match (nth_error inode.(block)
                       (N.to_nat blockNumInFile)) with
      | error => ErrorString "Data block not present"
      | value v => Found v
      end

     else if blockNumInFile <=? directAddressable
                                + indirect1Addressable then
      match (nth_error inode.(block) 12) with
      | error => ErrorString "Indirection block not present"
      | value indirectBlock => 
        walkIndirection disk superblock 
          (blockNumInFile - 12)
          (ba2Offset superblock indirectBlock) 
          O
      end

    else if blockNumInFile <=? directAddressable
                               + indirect1Addressable
                               + indirect2Addressable then
      match (nth_error inode.(block) 13)  with
      | error => ErrorString 
                   "Double indirection block not present"
      | value doubleIndirectBlock =>
        walkIndirection disk superblock
          (blockNumInFile - 12 - (blockSize / 4)) 
          (ba2Offset superblock doubleIndirectBlock) 
          (S O)
      end

    else 
      match (nth_error inode.(block) 14) with
      | error => ErrorString
                   "Triple indirection block not present"
      | value tripleIndirectBlock =>
        walkIndirection disk superblock 
          (blockNumInFile - directAddressable
                          - indirect1Addressable
                          - indirect2Addressable)
          (ba2Offset superblock tripleIndirectBlock)
          (S (S O))
      end
    ) _fflatmap_ (fun blockAddress =>
      disk (blockSize * blockAddress + (bytePos mod blockSize))
    ).

Lemma fetchInodeByte_subset :
  forall (sub super:Disk) (sb: SuperBlock) (inode: Inode) (bytePos: N)
         (byte: Byte),
    sub ⊆ super ->
      fetchInodeByte sub sb inode bytePos = Found byte ->
        fetchInodeByte super sb inode bytePos = Found byte.
Proof.
  intros sub super sb inode bytePos byte subset.
  unfold fetchInodeByte.
  destruct (size inode <=? bytePos); [ auto |].
  destruct (bytePos / blockSize sb <=? 12).
  (* Directly Addressable *)
    destruct (nth_error (block inode) (N.to_nat (bytePos / blockSize sb)));
      [| auto].
     unfold fetch_flatmap. apply subset.
  destruct (bytePos / blockSize sb <=? 12 + blockSize sb / 4).
  (* One level of indirection *)
    destruct (nth_error (block inode) 12); [| auto].
    intros. 
    apply found_fflatmap_found in H. destruct H as [aval [Haval H]].
    apply walkIndirection_subset with (1:=subset) in Haval. rewrite Haval.
    unfold fetch_flatmap. apply subset. assumption.
  destruct (bytePos / blockSize sb <=?
            12 + blockSize sb / 4 + blockSize sb * blockSize sb / 16); [| auto].
  (* Two levels of indirection *)
    destruct (nth_error (block inode) 13); [| auto].
    intros. 
    apply found_fflatmap_found in H. destruct H as [aval [Haval H]].
    apply walkIndirection_subset with (1:=subset) in Haval. rewrite Haval.
    unfold fetch_flatmap. apply subset. assumption.
  (* Three levels of indirection *)
    destruct (nth_error (block inode) 14); [| auto].
    intros. 
    apply found_fflatmap_found in H. destruct H as [aval [Haval H]].
    apply walkIndirection_subset with (1:=subset) in Haval. rewrite Haval.
    unfold fetch_flatmap. apply subset. assumption.
Qed.


(* ======= Delete ======= *)
Definition parseDeleted (disk: Disk) (superblock: SuperBlock)
  (groupdesc: GroupDescriptor) (inodeIndex: N) : @Fetch bool :=
  let inodeIndexInGroup := 
    (* 1-Indexed *)
    (inodeIndex - 1) mod superblock.(inodesPerGroup) in
  let bitmapStart := 
    ba2Offset superblock groupdesc.(inodeBitmap) in
  (* Fetch the allocation byte for this inode *)
  (disk (bitmapStart + (inodeIndexInGroup / 8))) 
    _fmap_ (fun allocationByte =>
    (* The bit associated with this inode is 0 *)
    match (allocationByte, inodeIndexInGroup mod 8) with
    | (Ascii b _ _ _ _ _ _ _, 0) => negb b
    | (Ascii _ b _ _ _ _ _ _, 1) => negb b
    | (Ascii _ _ b _ _ _ _ _, 2) => negb b
    | (Ascii _ _ _ b _ _ _ _, 3) => negb b
    | (Ascii _ _ _ _ b _ _ _, 4) => negb b
    | (Ascii _ _ _ _ _ b _ _, 5) => negb b
    | (Ascii _ _ _ _ _ _ b _, 6) => negb b
    | (Ascii _ _ _ _ _ _ _ b, 7) => negb b
    | _ => false  (* should never be reached *)
    end
  ).

Definition fileByte (disk: Disk) (inodeIndex offset: N)
  : @Fetch Byte :=
  (findAndParseSuperBlock disk) _fflatmap_ (fun superblock =>
  let groupId := ((inodeIndex - 1) (* One-indexed *)
                  / superblock.(inodesPerGroup)) in
  let inodeIndexInGroup :=
    (inodeIndex - 1) mod superblock.(inodesPerGroup) in
  (findAndParseGroupDescriptor disk superblock groupId) 
    _fflatmap_ (fun groupdesc =>
  (findAndParseInode disk superblock groupdesc inodeIndex)
    _fflatmap_ (fun inode =>
      fetchInodeByte disk superblock inode offset
  ))).

Definition findAndParseFile (disk: Disk) (inodeIndex: N) 
  : @Fetch File :=
  (findAndParseSuperBlock disk) _fflatmap_ (fun superblock =>
  let groupId := ((inodeIndex - 1) (* One-indexed *)
                  / superblock.(inodesPerGroup)) in
  let inodeIndexInGroup :=
    (inodeIndex - 1) mod superblock.(inodesPerGroup) in
  (findAndParseGroupDescriptor disk superblock groupId) 
    _fflatmap_ (fun groupdesc =>
  (findAndParseInode disk superblock groupdesc inodeIndex)
    _fflatmap_ (fun inode =>
  (parseDeleted disk superblock groupdesc inodeIndex)
    _fmap_ (fun deleted =>
    mkFile
      (FileIds.Ext2Id inodeIndex)
      inode.(size)
      deleted
      (value inode.(atime))
      (value inode.(mtime))
      (value inode.(ctime))
      (value inode.(dtime))
  )))).

