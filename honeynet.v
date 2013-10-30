(* How much effort is it to prove that a file exists,
   Either type with error/none/success,
   Basic Category Theory *)

(* Try to convert all of the tactics into definitions *)

Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.

Require Import ByteData.
Require Import Ext2.
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
  (mkFile None (* no need for an id *)
          1454080 (* uncompressed file size *)
          input.(deleted) 
          (fun (offset: Z) => find offset gunzipped_23)
          (* Fields not used; ignore them *)
          None None None None)).

Lemma flip_not_equal: forall (x y:Exc File),
  x <> y -> y <> x.
Proof.
  auto.
Qed.

Definition parseFileData (disk: Disk) (inodeIndex fileIndex: Z) : Exc Z :=
  (* Proceed as in parseFileFromInode *)
  (findAndParseSuperBlock disk) _flatmap_ (fun superblock =>
  let groupId := ((inodeIndex - 1) (* One-indexed *)
                  / superblock.(inodesPerGroup)) in
  let inodeIndexInGroup :=
    (inodeIndex - 1) mod superblock.(inodesPerGroup) in
  (findAndParseGroupDescriptor disk superblock groupId) 
    _flatmap_ (fun groupdesc =>
  (findAndParseInode disk superblock groupdesc inodeIndex)
    _flatmap_ (fun inode =>
  (parseDeleted disk superblock groupdesc inodeIndex) _flatmap_ (fun deleted =>
      (fetchInodeByte disk superblock inode fileIndex)
  )))).

(* Helper definitions which allow us to pull just one component from a file *)
Definition parseFileDeleted (disk: Disk) (inodeIndex: Z) : Exc bool :=
  (* Proceed as in parseFileFromInode *)
  (findAndParseSuperBlock disk) _flatmap_ (fun superblock =>
  (* One-indexed *)
  let groupId := ((inodeIndex - 1) / superblock.(inodesPerGroup)) in
  let inodeIndexInGroup := (inodeIndex - 1) mod superblock.(inodesPerGroup) in
  (findAndParseGroupDescriptor disk superblock groupId) _flatmap_ (fun groupdesc =>
  (findAndParseInode disk superblock groupdesc inodeIndex) _flatmap_ (fun inode =>
  (parseDeleted disk superblock groupdesc inodeIndex)
  ))).

Lemma deleted_means_deleted : forall (disk:Disk) (inodeIndex: Z) (del: bool), 
  parseFileDeleted disk inodeIndex = value del
  -> (findAndParseFile disk inodeIndex) _map_ (fun f => f.(deleted)) = value del.
Proof.
  intros disk inodeIndex del.
  unfold parseFileDeleted.
  unfold findAndParseFile.
  destruct (findAndParseSuperBlock disk) ; [|simpl; auto].
  simpl.
  destruct (findAndParseGroupDescriptor disk s 
              ((inodeIndex - 1) / inodesPerGroup s)) ; [|simpl; auto].
  simpl.
  destruct (findAndParseInode disk s g inodeIndex); [|simpl; auto]. simpl.
  destruct (parseDeleted disk s g inodeIndex); [|simpl; auto]. simpl.
  intros H. apply H.
Qed.

Lemma deleted_means_value: 
  forall (disk:Disk) (inodeIndex: Z), 
    parseFileDeleted disk inodeIndex <> error 
    -> findAndParseFile disk inodeIndex <> error.
Proof.
  intros disk inodeIndex.
  unfold parseFileDeleted.
  unfold findAndParseFile.
  destruct (findAndParseSuperBlock disk) ; [|simpl; auto].
  simpl.
  destruct (findAndParseGroupDescriptor disk s 
              ((inodeIndex - 1) / inodesPerGroup s)); 
    [|simpl; auto]. simpl.
  destruct (findAndParseInode disk s g inodeIndex); 
    [|simpl; auto]. simpl.
  destruct (parseDeleted disk s g inodeIndex); [|simpl; auto]. 
  simpl.
  intros _. discriminate.
Qed.

Ltac file_on_disk inodeIndex Heqe :=
  unfold isOnDisk; exists inodeIndex;
  unfold fileEq; rewrite <- Heqe;
  simpl; repeat (split; [reflexivity| ]);
  intros; reflexivity.

Ltac ext2_field_match disk inodeIndex field val Heqe :=
  assert ((findAndParseFile disk inodeIndex) _flatmap_ 
          (fun f => field f) = value val) as to_match;
    [vm_compute; reflexivity|];
  rewrite <- to_match; rewrite <- Heqe; vm_compute; reflexivity.



Ltac verify_ext2_event :=
  match goal with
  | |- exists file : File,
    isOnDisk file ?disk /\
    fileSystemId file = value ?fsId /\ ?field file = value ?val =>
    remember (findAndParseFile disk fsId) as e;
    destruct e as [f Heqe | f Heqe]; [ | contradict Heqe; apply flip_not_equal; 
      apply deleted_means_value; vm_compute; discriminate];
    exists f;
      split; [file_on_disk fsId Heqe|
      split; [
        ext2_field_match disk fsId fileSystemId fsId Heqe |
        ext2_field_match disk fsId field val
        Heqe]]
  end.

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
  repeat (destruct H; [rewrite <- H; verify_ext2_event|]).

  contradict H.

  (* monotonically increasing *)
  intros index.
  (* index < length of list (-1) *)
  repeat (destruct index; [vm_compute; intros; discriminate x0 |]).
  (* index is outside of the list *)
  vm_compute. intros.
  repeat (progress (apply le_pred in x; simpl in x;
                    try (contradict x; apply le_Sn_0))).
Qed.





Lemma byte_match: forall (disk: Disk) (inodeIndex fileIndex byte: Z),
  (fileIndex <? 0) = false ->
  (parseFileData disk inodeIndex fileIndex) = value byte ->
  (findAndParseFile disk inodeIndex) _flatmap_ (fun f =>
    f @[ fileIndex ]) = value byte.
Proof.
  intros disk inodeIndex fileIndex byte.
  unfold parseFileData.
  unfold findAndParseFile.
  destruct (findAndParseSuperBlock disk); [|simpl; auto].
  simpl.
  destruct (findAndParseGroupDescriptor disk s ((inodeIndex - 1) /
  inodesPerGroup s)) ; [|simpl; auto].
  simpl.
  destruct (findAndParseInode disk s g inodeIndex); [|simpl; auto]. simpl.
  destruct (parseDeleted disk s g inodeIndex); [|simpl; auto]. simpl.
  intros gt0. unfold fetchByte. simpl.
  rewrite gt0. intros H. apply H.
Qed.


Lemma borland_honeynet_file:
  exists (file: File),
  (isOnDisk file honeynet_image_a)
  /\ isDeleted file
  /\ isGzip file
  /\ Tar.looksLikeRootkit (gunzip_a file).
Proof.
  remember (findAndParseFile honeynet_image_a 23).
  destruct e; [ | contradict Heqe; apply flip_not_equal; 
      apply deleted_means_value; vm_compute; discriminate].
  exists f.
  split. 
    (* isOnDisk *)
    file_on_disk 23 Heqe.

  split.
    (* isDeleted *)
    unfold isDeleted.
    assert ((findAndParseFile honeynet_image_a 23) _map_ 
            (fun f => f.(deleted)) = value true).
    vm_compute. reflexivity.
    rewrite <- Heqe in H.
    simpl in H. injection H. auto.

  split.
    (* isGzip *)
    unfold isGzip. 
    split.
      assert ((findAndParseFile honeynet_image_a 23) _flatmap_
              (fun f => f @[ 0 ]) = value 31).
      vm_compute. reflexivity.
      rewrite <- Heqe in H. simpl in H. apply H.
    split.
      assert ((findAndParseFile honeynet_image_a 23) _flatmap_
              (fun f => f @[ 1 ]) = value 139).
      vm_compute. reflexivity.
      rewrite <- Heqe in H. simpl in H. apply H.

      assert ((findAndParseFile honeynet_image_a 23) _flatmap_
              (fun f => f @[ 2 ]) = value 8).
      vm_compute. reflexivity.
      rewrite <- Heqe in H. simpl in H. apply H.
      
    unfold looksLikeRootkit.
    exists (ascii2Bytes "last/ssh"); exists (ascii2Bytes "last/top").
      split. vm_compute. repeat (try (left; reflexivity); right).
      split. vm_compute. repeat (try (left; reflexivity); right).
      split. vm_compute. repeat (try (left; reflexivity); right).
      split. vm_compute. repeat (try (left; reflexivity); right).
    vm_compute. intros contra. inversion contra.
Qed.
