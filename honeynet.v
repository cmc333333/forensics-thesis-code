(* How much effort is it to prove that a file exists,
   Either type with error/none/success,
   Basic Category Theory *)

(* Try to convert all of the tactics into definitions *)

Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.

Require Import ByteData.
Require Import Ext2.
Require Import Ext2Lemmas.
Require Import Fetch.
Require Import File.
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
  (mkFile None (* no need for an id *)
          1454080 (* uncompressed file size *)
          input.(deleted) 
          asDisk
          (* Fields not used; ignore them *)
          None None None None)).



Lemma lee_honeynet_file:
  (Timeline.isSound (
    (* Mar 16 01 12:36:48 *)
      (* rootkit lk.tar.gz downloaded *)
        (FileModification 984706608 23)
    (* Mar 16 01 12:44:50 *)
      (* Gunzip and Untar rootkit lk.tar.gz *)
        :: (FileAccess 984707090 23)
      (* change ownership of rootkit files to root.root *)
        :: (FileAccess 984707102 30130)
      (* deletion of original /bin/netstat *)
        :: (FileDeletion 984707102 30188)
      (* insertion of trojan netstat *)
        :: (FileCreation 984707102 2056) 
      (* deletion of original /bin/ps *)
        :: (FileDeletion 984707102 30191)
      (* insertion of trojan ps *)
        :: (FileCreation 984707102 2055) 
      (* deletion of origin /sbin/ifconfig *)
        :: (FileDeletion 984707102 48284)
      (* insertion of trojan ifconfig *)
        :: (FileCreation 984707102 2057) 
    (* Mar 16 01 12:45:03 *)
      (* the copy of service files to /etc *)
        :: (FileAccess 984707103 30131)  
      (* hackers services file copied on top of original *)
        :: (FileCreation 984707103 26121)
    (* Mar 16 01 12:45:05 *)
      (* deletion of rootkit lk.tar.gz *)
        :: (FileDeletion 984707105 23)   
    :: nil)
    honeynet_image_a
  ).
Proof.
  unfold isSound. split.

  (* foundOn - verify each event *)
  unfold foundOn. intros. simpl in H.
  repeat (destruct H; [
    rewrite <- H; apply verify_ext2_event; vm_compute; reflexivity|]).

  contradict H.

  (* monotonically increasing *)
  intros index.
  (* index < length of list (-1) *)
  repeat (destruct index; [vm_compute; intros; discriminate x0 |]).
  (* index is outside of the list *)
  vm_compute. intros.
  repeat (apply le_pred in x; simpl in x;
                    try (contradict x; apply le_Sn_0)).
Qed.

Lemma borland_honeynet_file:
  exists (file: File),
  (isOnDisk file honeynet_image_a)
  /\ isDeleted file
  /\ isGzip file
  /\ Tar.looksLikeRootkit (gunzip_a file).
Proof.
  remember (findAndParseFile honeynet_image_a 23).
  destruct f; [
    | contradict Heqf; apply ext2_fetch_excl_middle; apply ext2_avoid_compute;
      vm_compute; eauto
    | contradict Heqf; apply ext2_fetch_excl_middle; apply ext2_avoid_compute;
      vm_compute; eauto].
  exists f.
  split. 
    (* isOnDisk *)
    apply ext2_file_on_disk in Heqf. apply Heqf.

  split.
    (* isDeleted *)
    unfold isDeleted.
    apply ext2_field_match with (disk := honeynet_image_a) (inodeIndex := 23).
    split; [auto | vm_compute; reflexivity].

  split.
    (* isGzip *)
    unfold isGzip. 
    unfold fetchByte. simpl.
    split.
      apply ext2_byte_match with (disk := honeynet_image_a) (inodeIndex := 23).
      split ; [auto | vm_compute; reflexivity].
    split.
      apply ext2_byte_match with (disk := honeynet_image_a) (inodeIndex := 23).
      split ; [auto | vm_compute; reflexivity].

      apply ext2_byte_match with (disk := honeynet_image_a) (inodeIndex := 23).
      split ; [auto | vm_compute; reflexivity].
      
    unfold looksLikeRootkit.
    exists (ascii2Bytes "last/ssh"); exists (ascii2Bytes "last/top").
      set (fileNames := parseFileNames (gunzip_a f)).
      vm_compute in fileNames.
      split. vm_compute. repeat (try (left; reflexivity); right).
      split. vm_compute. repeat (try (left; reflexivity); right).
      clear fileNames.
      split. vm_compute. repeat (try (left; reflexivity); right).
      split. vm_compute. repeat (try (left; reflexivity); right).
    vm_compute. intros contra. inversion contra.
Qed.
