(* How much effort is it to prove that a file exists,
   Either type with error/none/success,
   Basic Category Theory *)

(* Try to convert all of the tactics into definitions *)

Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
(* Require Evm_compute. *)

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



Lemma lee_honeynet_file:
  (Timeline.isSound (
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
    :: nil)
    honeynet_image_a
  ).
Proof.
  unfold isSound. split.

  (* foundOn - verify each event *)
  unfold foundOn. intros. simpl in H.
  Show Proof.
  repeat (destruct H; [
    rewrite <- H; apply verify_ext2_event; vm_compute; reflexivity|]).
  Show Proof.

  contradict H.

  (* monotonically increasing *)
  intros index.
  (* index < length of list (-1) *)
  repeat (destruct index; [vm_compute; intros; discriminate x0 |]).
  (* index is outside of the list *)
  vm_compute. intros.
  repeat (apply le_pred in x; simpl in x;
                    try (contradict x; apply le_Sn_0)).
  Show Proof.
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
