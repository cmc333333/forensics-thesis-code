(* How much effort is it to prove that a file exists,
   Either type with error/none/success,
   Basic Category Theory *)

(* Try to convert all of the tactics into definitions *)

Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.

Require Import ByteData.
Require Import Ext2.
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

Lemma flip_not_equal: forall (x y:@Fetch File),
  x <> y -> y <> x.
Proof.
  auto.
Qed.

Definition parseFileData (disk: Disk) (inodeIndex fileIndex: Z) : @Fetch Z :=
  (* Proceed as in parseFileFromInode *)
  (findAndParseSuperBlock disk) _fflatmap_ (fun superblock =>
  let groupId := ((inodeIndex - 1) (* One-indexed *)
                  / superblock.(inodesPerGroup)) in
  let inodeIndexInGroup :=
    (inodeIndex - 1) mod superblock.(inodesPerGroup) in
  (findAndParseGroupDescriptor disk superblock groupId) 
    _fflatmap_ (fun groupdesc =>
  (findAndParseInode disk superblock groupdesc inodeIndex)
    _fflatmap_ (fun inode =>
  (parseDeleted disk superblock groupdesc inodeIndex) _fflatmap_ (fun deleted =>
      (fetchInodeByte disk superblock inode fileIndex)
  )))).

(* Helper definitions which allow us to pull just one component from a file *)
Definition parseFileDeleted (disk: Disk) (inodeIndex: Z) : @Fetch bool :=
  (* Proceed as in parseFileFromInode *)
  (findAndParseSuperBlock disk) _fflatmap_ (fun superblock =>
  (* One-indexed *)
  let groupId := ((inodeIndex - 1) / superblock.(inodesPerGroup)) in
  let inodeIndexInGroup := (inodeIndex - 1) mod superblock.(inodesPerGroup) in
  (findAndParseGroupDescriptor disk superblock groupId) _fflatmap_ (fun groupdesc =>
  (findAndParseInode disk superblock groupdesc inodeIndex) _fflatmap_ (fun inode =>
  (parseDeleted disk superblock groupdesc inodeIndex)
  ))).

Lemma deleted_means_deleted : forall (disk:Disk) (inodeIndex: Z) (del: bool), 
  parseFileDeleted disk inodeIndex = Found del
  -> (findAndParseFile disk inodeIndex) _fmap_ (fun f => f.(deleted)) = Found del.
Proof.
  intros disk inodeIndex del.
  unfold parseFileDeleted.
  unfold findAndParseFile.
  destruct (findAndParseSuperBlock disk) ; [|simpl; auto |simpl; auto].
  simpl.
  destruct (findAndParseGroupDescriptor disk s 
              ((inodeIndex - 1) / inodesPerGroup s)) 
              ; [|simpl; auto |simpl; auto].
  simpl.
  destruct (findAndParseInode disk s g inodeIndex); [|simpl; auto |simpl; auto]. 
    simpl.
  destruct (parseDeleted disk s g inodeIndex); [|simpl; auto |simpl; auto].
    simpl.
  intros H. apply H.
Qed.

Lemma deleted_means_value: 
  forall (disk:Disk) (inodeIndex: Z), 
    (exists (b:bool), parseFileDeleted disk inodeIndex = Found b)
    -> (exists (f:File), findAndParseFile disk inodeIndex = Found f).
Proof.
  intros disk inodeIndex.
  unfold parseFileDeleted.
  unfold findAndParseFile.
  destruct (findAndParseSuperBlock disk); [
    | simpl; intros assump; inversion assump; discriminate H
    | simpl; intros assump; inversion assump; discriminate H].
  simpl.
  destruct (findAndParseGroupDescriptor disk s 
              ((inodeIndex - 1) / inodesPerGroup s)); [
    | simpl; intros assump; inversion assump; discriminate H
    | simpl; intros assump; inversion assump; discriminate H]. simpl.
  destruct (findAndParseInode disk s g inodeIndex); [
    | simpl; intros assump; inversion assump; discriminate H
    | simpl; intros assump; inversion assump; discriminate H]. simpl.
  destruct (parseDeleted disk s g inodeIndex); [
    | simpl; intros assump; inversion assump; discriminate H
    | simpl; intros assump; inversion assump; discriminate H]. simpl.
  intros _. exists (mkFile (value inodeIndex)
                           (size i)
                           b 
                           (fetchInodeByte disk s i)
                           (value (atime i))
                           (value (mtime i))
                           (value (ctime i))
                           (value (dtime i))). auto.
Qed.

Ltac file_on_disk inodeIndex Heqe :=
  unfold isOnDisk; exists inodeIndex;
  unfold fileEq; rewrite <- Heqe;
  simpl; repeat (split; [reflexivity| ]);
  intros; reflexivity.



Definition found_eq {X:Type} : forall (x y:X), Found x = Found y -> x = y.
  Proof.
  intros. injection H. auto.
Qed.

Ltac ext2_field_match disk inodeIndex field val T Heqe :=
  assert ((findAndParseFile disk inodeIndex) _fmap_ 
          (fun f => field f) = @Found T val) as to_match;
    [vm_compute; reflexivity|];
  apply found_eq;
  rewrite <- to_match; rewrite <- Heqe; vm_compute; reflexivity.

Lemma verify_ext2_event1 (disk:Disk) (inodeIndex:Z): 
  (exists (f:File), findAndParseFile disk inodeIndex = Found f)
  -> (forall (z:Z), MissingAt z <> findAndParseFile disk inodeIndex)
      /\ (forall (s:String.string), ErrorString s <> findAndParseFile disk inodeIndex).
Proof.
  intros H.
  destruct (findAndParseFile disk inodeIndex).
  split; [discriminate | discriminate].
  split; [inversion H; inversion H0 | discriminate].
  split; [discriminate | inversion H; inversion H0].
Qed.

Ltac verify_ext2_event :=
  match goal with
  | |- exists file : File,
    isOnDisk file ?disk /\
    fileSystemId file = value ?fsId /\ ?field file = value ?val =>
    remember (findAndParseFile disk fsId) as e;
    destruct e as [f Heqe | z Heqe | s Heqe]; [ 
      | contradict Heqe; apply verify_ext2_event1;
        apply deleted_means_value; vm_compute; eauto; reflexivity
      | contradict Heqe; apply verify_ext2_event1;
        apply deleted_means_value; vm_compute; eauto; reflexivity];
    exists f;
      split; [file_on_disk fsId Heqe|
      split; [
        ext2_field_match disk fsId fileSystemId (value fsId) (Exc Z) Heqe |
        ext2_field_match disk fsId field (value val) (Exc Z) Heqe
      ]]
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
  (parseFileData disk inodeIndex fileIndex) = Found byte ->
  (findAndParseFile disk inodeIndex) _fflatmap_ (fun f =>
    f @[ fileIndex ]) = Found byte.
Proof.
  intros disk inodeIndex fileIndex byte.
  unfold parseFileData.
  unfold findAndParseFile.
  destruct (findAndParseSuperBlock disk); [|simpl; auto|simpl; auto].
  simpl.
  destruct (findAndParseGroupDescriptor disk s ((inodeIndex - 1) /
  inodesPerGroup s)) ; [|simpl; auto|simpl; auto].
  simpl.
  destruct (findAndParseInode disk s g inodeIndex); [|simpl; auto|simpl; auto]. 
  simpl.
  destruct (parseDeleted disk s g inodeIndex); [|simpl; auto|simpl; auto]. simpl.
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
  destruct f; [
    | contradict Heqf; apply verify_ext2_event1; apply deleted_means_value;
      vm_compute; eauto
    | contradict Heqf; apply verify_ext2_event1; apply deleted_means_value;
      vm_compute; eauto].
  exists f.
  split. 
    (* isOnDisk *)
    file_on_disk 23 Heqf.

  split.
    (* isDeleted *)
    unfold isDeleted.
    assert ((findAndParseFile honeynet_image_a 23) _fmap_ 
            (fun f => f.(deleted)) = Found true).
    vm_compute. reflexivity.
    rewrite <- Heqf in H.
    simpl in H. injection H. auto.

  split.
    (* isGzip *)
    unfold isGzip. 
    split.
      assert ((findAndParseFile honeynet_image_a 23) _fflatmap_
              (fun f => f @[ 0 ]) = Found 31).
      vm_compute. reflexivity.
      rewrite <- Heqf in H. simpl in H. apply H.
    split.
      assert ((findAndParseFile honeynet_image_a 23) _fflatmap_
              (fun f => f @[ 1 ]) = Found 139).
      vm_compute. reflexivity.
      rewrite <- Heqf in H. simpl in H. apply H.

      assert ((findAndParseFile honeynet_image_a 23) _fflatmap_
              (fun f => f @[ 2 ]) = Found 8).
      vm_compute. reflexivity.
      rewrite <- Heqf in H. simpl in H. apply H.
      
    unfold looksLikeRootkit.
    exists (ascii2Bytes "last/ssh"); exists (ascii2Bytes "last/top").
      split. vm_compute. repeat (try (left; reflexivity); right).
      split. vm_compute. repeat (try (left; reflexivity); right).
      split. vm_compute. repeat (try (left; reflexivity); right).
      split. vm_compute. repeat (try (left; reflexivity); right).
    vm_compute. intros contra. inversion contra.
Qed.
