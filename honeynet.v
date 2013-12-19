Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.

Require Import ByteData.
Require Import Ext2.
Require Import Ext2Lemmas.
Require Import Fetch.
Require Import File.
Require Import FileData.
Require Import FileNames.
Require Import FileSystems.
Require Import FileTypes.
Require Import Tar.
Require Import Timeline.
Require Import Util.

Require Import example_images.

Open Local Scope Z.

Definition honeynet_image_a : Disk := honeynet_map.
(* All gunzip operations return the file mentioned *)
Definition gunzip_a := (fun (input: File) => 
  let asDisk := Disk_of_Map_Z_Z gunzipped_23 in
  (mkFile (FileSystems.MockFS asDisk)
          1454080 (* uncompressed file size *)
          input.(deleted) 
          (* Fields not used; ignore them *)
          None None None None)).

Definition lee_timeline :=
  (* Mar 16 01 12:36:48 *)
    (* rootkit lk.tar.gz downloaded *)
      (FileModification 984706608 (Ext2FS 23))
  (* Mar 16 01 12:44:50 *)
    (* Gunzip and Untar rootkit lk.tar.gz *)
      :: (FileAccess 984707090 (Ext2FS 23))
    (* change ownership of rootkit files to root.root *)
      :: (FileAccess 984707102 (Ext2FS 30130))
    (* deletion of original /bin/netstat *)
      :: (FileDeletion 984707102 (Ext2FS 30188))
    (* insertion of trojan netstat *)
      :: (FileCreation 984707102 (Ext2FS 2056))
    (* deletion of original /bin/ps *)
      :: (FileDeletion 984707102 (Ext2FS 30191))
    (* insertion of trojan ps *)
      :: (FileCreation 984707102 (Ext2FS 2055))
    (* deletion of origin /sbin/ifconfig *)
      :: (FileDeletion 984707102 (Ext2FS 48284))
    (* insertion of trojan ifconfig *)
      :: (FileCreation 984707102 (Ext2FS 2057))
  (* Mar 16 01 12:45:03 *)
    (* the copy of service files to /etc *)
      :: (FileAccess 984707103 (Ext2FS 30131))
    (* hackers services file copied on top of original *)
      :: (FileCreation 984707103 (Ext2FS 26121))
  (* Mar 16 01 12:45:05 *)
    (* deletion of rootkit lk.tar.gz *)
      :: (FileDeletion 984707105 (Ext2FS 23))
  :: nil.

Lemma lee_honeynet_file:
  Timeline.isSound lee_timeline honeynet_image_a.
Proof.
  unfold isSound. intros pair H.

  simpl in H.
  repeat (destruct H; [
    rewrite <- H; simpl; split; [ (* first event is on disk *)
        try (apply verify_ext2_access); try (apply verify_ext2_modification);
        try (apply verify_ext2_creation); try (apply verify_ext2_deletion);
        vm_compute; reflexivity
      | split; [ (* second event is on disk *)
          try (apply verify_ext2_access); try (apply verify_ext2_modification);
          try (apply verify_ext2_creation); try (apply verify_ext2_deletion);
          vm_compute; reflexivity
        | (* beforeOrConcurrent *)
          unfold beforeOrConcurrent; simpl; omega ]] |]).
  contradict H.
Qed.

Lemma borland_honeynet_file:
  exists f: File,
  isOnDisk f honeynet_image_a
  /\ isDeleted f
  /\ isGzip f honeynet_image_a
  /\ Tar.looksLikeRootkit (gunzip_a f) honeynet_image_a.
  Proof.
    set (file := mkFile (Ext2FS 23)
                         520333
                         true
                        (Some 984707090)
                        (Some 984706608)
                        (Some 984707105)
                        (Some 984707105)).
    exists file.
    split. vm_compute. reflexivity.
    Show Proof.
    split. reflexivity.
    Show Proof.
    split. vm_compute. repeat (split ; [reflexivity| ]); reflexivity.
    Show Proof.
    unfold looksLikeRootkit.
    exists (ascii2Bytes "last/ssh"); exists (ascii2Bytes "last/top").
    Show Proof.
    set (fileNames := parseFileNames (gunzip_a file) honeynet_image_a).
    vm_compute in fileNames.
    Show Proof.
    split. vm_compute. reflexivity.
    Show Proof.
    split. vm_compute. reflexivity.
    Show Proof.
    split. vm_compute. repeat (try (left; reflexivity); right).
    Show Proof.
    split. vm_compute. repeat (try (left; reflexivity); right).
    Show Proof.
    vm_compute. reflexivity.
    Show Proof.
Qed.
