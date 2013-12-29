Require Import Coq.ZArith.ZArith.

Require Import ByteData.
Require Import Fetch.
Require Import File.
Require Import Util.

Open Local Scope Z.

(* Field names based on http://www.nongnu.org/ext2-doc/ext2.html *)

(* Block Address will come up again and again *)
Definition BA := Z.


(* ======= SuperBlock ======= *)
Structure SuperBlock := mkSuperBlock {
  inodesCount: Z;
  blocksCount: Z;
  rBlocksCount: Z;
  freeBlocksCount: Z;
  freeInodesCount: Z;
  firstDataBlock: BA;
  logBlockSize: Z;
  logFragSize: Z;
  blocksPerGroup: Z;
  fragsPerGroup: Z;
  inodesPerGroup: Z;
  mTime: Z;
  wTime: Z;
  mntCount: Z;
  maxMntCount: Z;
  magic: Z;
  state: Z;
  errors: Z;
  minorRevLevel: Z;
  lastCheck: Z;
  checkinterval: Z;
  creatorOS: Z;
  revLevel: Z;
  defResuid: Z;
  defResgid: Z;
  (* EXT2_DYNAMIC_REV Specific *)
  firstIno: Z;
  inodeSize: Z;
  blockGroupNr: Z;
  featureCompat: Z;
  featureIncompat: Z;
  featureROCompat: Z;
  uuid: list Z;
  volumeName: list Z;
  lastMounted: list Z;
  algoBitmap: Z;
  (* Performance Hints *)
  preallocBlocks: Z;
  preallocDirBlocks: Z;
  (* Journaling Support *)
  journalUUID: Z;
  journalInum: Z;
  journalDev: Z;
  lastOrphan: Z;
  (* Directory Indexing Support *)
  hashSeed: Z;
  defHashVersion: Z;
  (* Other options *)
  defaultMountOptions: Z;
  firstMetaBg: Z
}.

Definition findAndParseSuperBlock (disk: Disk): @Fetch SuperBlock :=
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
      volumeName
      lastMounted
      algoBitmap
      preallocBlocks
      preallocDirBlocks
      journalUUID
      journalInum
      journalDev
      lastOrphan
      hashSeed
      defHashVersion
      defaultMountOptions
      firstMetaBg
  ))))))))))))))))))))))))))))))))))))))))))))).

Definition blockSize (superblock: SuperBlock) : Z :=
  Z.shiftl 1024 superblock.(logBlockSize).

Definition ba2Offset (superblock: SuperBlock) (blockAddress: BA)
  := (blockSize superblock) * blockAddress.


(* ======= GroupDescriptor ======= *)
Structure GroupDescriptor := mkGroupDescriptor {
  blockBitmap: BA;
  inodeBitmap: BA;
  inodeTable: BA;
  gdFreeBlocksCount: Z;
  gdFreeInodesCount: Z;
  usedDirsCount: Z
}.

Definition findAndParseGroupDescriptor 
  (disk: Disk) (superblock: SuperBlock) (groupId: Z)
  : @Fetch GroupDescriptor :=
  let groupBlockArrayBA := if (blockSize superblock >? 1024)
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


(* ======= INode ======= *)
Structure Inode := mkInode {
  mode: Z;
  uid: Z;
  size: Z;
  atime: Z;
  ctime: Z;
  mtime: Z;
  dtime: Z;
  gid: Z;
  linksCount: Z;
  blocks: Z;
  flags: Z;
  osd1: Z;
  block: list BA;
  generation: Z;
  fileACL: Z;
  dirACL: Z;
  faddr: Z;
  osd2: Z
}.

Definition findAndParseInode (disk: Disk)
  (superblock: SuperBlock) (groupdesc: GroupDescriptor)
  (inodeIndex: Z): @Fetch Inode :=
  (* Check for valid Inode *)
  if (inodeIndex >=? superblock.(inodesCount))
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
    (seq_lendu disk 92 4) _fflatmap_ (fun doubleIndirectBlock =>
    (seq_lendu disk 96 4) _fflatmap_ (fun tripleIndirectBlock =>
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


(* ======= Fetch Arbitrary Bytes For An Inode ======= *)
(* Recursive function for dealing with levels of indirection *)
Fixpoint walkIndirection (disk: Disk) (superblock: SuperBlock)
  (blockNumber indirectionPos: Z) (indirectionLevel: nat) 
  : @Fetch Z :=
  match indirectionLevel with
  | O => 
      let bytePosition := (indirectionPos + 4 * blockNumber) in
      (seq_lendu disk bytePosition 4)
  | S nextIndirectionLevel =>
    (* Type conversion *)
    let exponent := Z.of_nat indirectionLevel in
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


Definition fetchInodeByte (disk: Disk) (superblock: SuperBlock) 
  (inode: Inode) (bytePos: Z): @Fetch Z :=
  if inode.(size) <=? bytePos then 
    MissingAt bytePos
  else 
    let blockSize := (blockSize superblock) in
    let blockNumInFile := bytePos / blockSize in
    let directAddressable := 12 in
    let indirect1Addressable := blockSize / 4 in
    let indirect2Addressable := (blockSize * blockSize) / 16 in

    (if blockNumInFile <=? directAddressable then
      match (nth_error inode.(block) (Z.to_nat blockNumInFile)) with
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
      | error => ErrorString "Double indirection block not present"
      | value doubleIndirectBlock =>
        walkIndirection disk superblock
          (blockNumInFile - 12 - (blockSize / 4)) 
          (ba2Offset superblock doubleIndirectBlock) 
          (S O)
      end

    else 
      match (nth_error inode.(block) 14) with
      | error => ErrorString "Triple indirection block not present"
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


(* ======= Delete ======= *)
Definition parseDeleted (disk: Disk) (superblock: SuperBlock)
  (groupdesc: GroupDescriptor) (inodeIndex: Z) : @Fetch bool :=
  let inodeIndexInGroup := 
    (* 1-Indexed *)
    (inodeIndex - 1) mod superblock.(inodesPerGroup) in
  let bitmapStart := 
    ba2Offset superblock groupdesc.(inodeBitmap) in
  (* Fetch the allocation byte for this inode *)
  (disk (bitmapStart + (inodeIndexInGroup / 8))) 
    _fmap_ (fun allocationByte =>
    (* The bit associated with this inode is 0 *)
    (negb (Z.testbit allocationByte
                     (inodeIndexInGroup mod 8)))
  ).

Definition fileByte (disk: Disk) (inodeIndex offset: Z)
  : @Fetch Z :=
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

Definition findAndParseFile (disk: Disk) (inodeIndex: Z) 
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

