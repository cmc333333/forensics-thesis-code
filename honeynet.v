Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Require Import ByteData.
Require Import DiskSubset.
Require Import Ext2.
Require Import Fetch.
Require Import File.
Require Import FileData.
Require Import FileNames.
Require Import FileIds.
Require Import FileTypes.
Require Import HoneynetDefinitions.
Require Import Tar.
Require Import Timeline.
Require Import Util.

Require Import example_images.

Local Open Scope N.

Local Open Scope char.
Fixpoint fill_disk (level:nat) : Map_N_Byte :=
  match level with
  | O => honeynet_map
  | S level_minus_one =>
      let initial := (N.of_nat level_minus_one) * 25 + 100000000 in
      (MN.add (0 + initial) "000" (MN.add (1 + initial) "000"
      (MN.add (2 + initial) "000" (MN.add (3 + initial) "000"
      (MN.add (4 + initial) "000" (MN.add (5 + initial) "000"
      (MN.add (6 + initial) "000" (MN.add (7 + initial) "000"
      (MN.add (8 + initial) "000" (MN.add (9 + initial) "000"
      (MN.add (10 + initial) "000" (MN.add (11 + initial) "000"
      (MN.add (12 + initial) "000" (MN.add (13 + initial) "000"
      (MN.add (14 + initial) "000" (MN.add (15 + initial) "000"
      (MN.add (16 + initial) "000" (MN.add (17 + initial) "000"
      (MN.add (18 + initial) "000" (MN.add (19 + initial) "000"
      (MN.add (20 + initial) "000" (MN.add (21 + initial) "000"
      (MN.add (22 + initial) "000" (MN.add (23 + initial) "000"
      (MN.add (24 + initial) "000"
      (fill_disk level_minus_one))))))))))))))))))))))))))
    end.
Local Open Scope string.

Definition honeynet_image_partial : Disk := fill_disk 0%nat.
(* All gunzip operations return the file mentioned *)
Definition gunzipped_partial : File := mkFile 
  (FileIds.MockId (MN.elements gunzipped_23))
  1454080 (* uncompressed file size *)
  true
  (* Fields not used; ignore them *)
  None None None None.

Definition lee_timeline :=
  (* Mar 16 01 12:36:48 *)
    (* rootkit lk.tar.gz downloaded *)
      (FileModification 984706608 (Ext2Id 23))
  (* Mar 16 01 12:44:50 *)
    (* Gunzip and Untar rootkit lk.tar.gz *)
      :: (FileAccess 984707090 (Ext2Id 23))
    (* change ownership of rootkit files to root.root *)
      :: (FileAccess 984707102 (Ext2Id 30130))
    (* deletion of original /bin/netstat *)
      :: (FileDeletion 984707102 (Ext2Id 30188))
    (* insertion of trojan netstat *)
      :: (FileCreation 984707102 (Ext2Id 2056))
    (* deletion of original /bin/ps *)
      :: (FileDeletion 984707102 (Ext2Id 30191))
    (* insertion of trojan ps *)
      :: (FileCreation 984707102 (Ext2Id 2055))
    (* deletion of origin /sbin/ifconfig *)
      :: (FileDeletion 984707102 (Ext2Id 48284))
    (* insertion of trojan ifconfig *)
      :: (FileCreation 984707102 (Ext2Id 2057))
  (* Mar 16 01 12:45:03 *)
    (* the copy of service files to /etc *)
      :: (FileAccess 984707103 (Ext2Id 30131))
    (* hackers services file copied on top of original *)
      :: (FileCreation 984707103 (Ext2Id 26121))
  (* Mar 16 01 12:45:05 *)
    (* deletion of rootkit lk.tar.gz *)
      :: (FileDeletion 984707105 (Ext2Id 23))
  :: nil.

Definition file23 := mkFile (Ext2Id 23) 520333 true 
                            (Some 984707090) 
                            (Some 984706608)
                            (Some 984707105)
                            (Some 984707105).
Definition file2055 := mkFile (Ext2Id 2055) 33280 false
                              (Some 984707090) 
                              (Some 983201013)
                              (Some 984707102)
                              (Some 0).
Definition file2056 := mkFile (Ext2Id 2056) 35300 false
                              (Some 984707090) 
                              (Some 983201022)
                              (Some 984707102)
                              (Some 0).
Definition file2057 := mkFile (Ext2Id 2057) 19840 false
                              (Some 984707105)
                              (Some 983201027)
                              (Some 984707102)
                              (Some 0).
Definition file26121 := mkFile (Ext2Id 26121) 11407 false
                               (Some 984753658)
                               (Some 984707103)
                               (Some 984707103)
                               (Some 0).
Definition file30130 := mkFile (Ext2Id 30130) 11952 false
                               (Some 984707102) 
                               (Some 952479772)
                               (Some 984654676)
                               (Some 0).
Definition file30131 := mkFile (Ext2Id 30131) 33392 false
                               (Some 984707103)
                               (Some 952479772)
                               (Some 984654676)
                               (Some 0).
Definition file30188 := mkFile (Ext2Id 30188) 66736 true
                               (Some 984677103) 
                               (Some 952425102)
                               (Some 984707102)
                               (Some 984707102).
Definition file30191 := mkFile (Ext2Id 30191) 60080 true
                               (Some 984677352) 
                               (Some 952452206)
                               (Some 984707102)
                               (Some 984707102).
Definition file48284 := mkFile (Ext2Id 48284) 42736 true
                               (Some 984677122)
                               (Some 952425102)
                               (Some 984707102)
                               (Some 984707102).

Lemma lee_honeynet_file:
  honeynet_image_partial ⊆ OriginalDisk ->
    Timeline.isSound lee_timeline OriginalDisk.
Proof.
  intros subset. apply isSound_subset with (1:=subset).
  set (files := file23 :: file23 :: file30130 :: file30188 
                :: file2056 :: file30191 :: file2055
                :: file48284 :: file2057 :: file30131
                :: file26121 :: file23 :: nil).
  apply isSound_reflection with (files := files).
  vm_compute. reflexivity.
Qed.

Definition maliciousFileName1 := "last/ssh".
Definition maliciousFileName2 := "last/top".

(* Turn this into a  Investigation of Computation of Forensics; it's easy to
make definitions, but those don't work well because we need proof by reflexion

Reflection - makes tactics smaller; makes proof terms smaller
*)

Lemma borland_honeynet_file:
  honeynet_image_partial ⊆ OriginalDisk ->
    (gunzip file23) = gunzipped_partial ->
      borland_rootkit OriginalDisk.
  Proof.
    intros subset H_gunzip.
    apply borland_rootkit_subset with (1:=subset).
    revert H_gunzip.
    apply borland_reflection 
      with (file := file23) (gunzipped := gunzipped_partial)
           (filename1 := maliciousFileName1) 
           (filename2 := maliciousFileName2).
    vm_compute. reflexivity.
Qed.
