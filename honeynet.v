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

Lemma avoid_compute:
  forall (disk:Disk) (inodeIndex: Z),
    (exists (b:bool),
      (findAndParseFile disk inodeIndex) _fmap_ (fun f => deleted f) = Found b)
    -> exists (file:File), findAndParseFile disk inodeIndex = Found file.
  intros disk inodeIndex.
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
  intros _. eauto.
Qed.

Lemma ext2_file_on_disk: 
  forall (disk:Disk) (file:File) (inodeIndex:Z),
  Found file = findAndParseFile disk inodeIndex
  -> isOnDisk file disk.
Proof.
  intros.
  unfold isOnDisk. exists inodeIndex.
  unfold fileEq. rewrite <- H.
  split; [reflexivity | split; [reflexivity|]].
  intros. reflexivity.
Qed.


Definition found_eq {X:Type} : forall (x y:X), Found x = Found y -> x = y.
  Proof.
  intros. injection H. auto.
Qed.

Lemma ext2_field_match (X:Type):
  forall (fn: File->X) (x:X) (file:File) (disk:Disk) (inodeIndex:Z),
    (Found file = findAndParseFile disk inodeIndex
    /\ (findAndParseFile disk inodeIndex) _fmap_ (fn) = @Found X x)
    -> fn file = x.
Proof.
  intros. destruct H.
  apply found_eq.
  rewrite <- H0. rewrite <- H. vm_compute. reflexivity.
Qed.

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

Lemma verify_ext2_event2:
  forall (disk:Disk) (inodeIndex:Z) (file:File),
    findAndParseFile disk inodeIndex = Found file
    -> fileSystemId file = value inodeIndex.
Proof.
  intros.
    apply ext2_field_match with (disk := disk) (inodeIndex := inodeIndex).
      split. auto. remember (findAndParseFile disk inodeIndex) as parse.
        unfold findAndParseFile in Heqparse.
        destruct (findAndParseSuperBlock disk) in Heqparse;
          [| simpl in Heqparse; rewrite Heqparse in H; discriminate H
           | simpl in Heqparse; rewrite Heqparse in H; discriminate H].
        simpl in Heqparse.
        destruct (findAndParseGroupDescriptor disk s) in Heqparse;
          [| simpl in Heqparse; rewrite Heqparse in H; discriminate H
           | simpl in Heqparse; rewrite Heqparse in H; discriminate H].
        simpl in Heqparse.
        destruct (findAndParseInode disk s g inodeIndex) in Heqparse;
          [| simpl in Heqparse; rewrite Heqparse in H; discriminate H
           | simpl in Heqparse; rewrite Heqparse in H; discriminate H].
        simpl in Heqparse.
        destruct (parseDeleted disk s g inodeIndex) in Heqparse;
          [| simpl in Heqparse; rewrite Heqparse in H; discriminate H
           | simpl in Heqparse; rewrite Heqparse in H; discriminate H].
        simpl in Heqparse.
        rewrite Heqparse. auto.
Qed.

Lemma verify_ext2_event3 {T: Type}:
  forall (disk:Disk) (inodeIndex: Z) (fn: File->T) (val: T),
    ((findAndParseFile disk inodeIndex) _fmap_ fn = Found val)
    -> (exists (file:File),
        isOnDisk file disk
        /\ fileSystemId file = value inodeIndex
        /\ fn file = val).
Proof.
  intros. remember (findAndParseFile disk inodeIndex) as e.
  destruct e as [f Heq | z Heq | s Heq]; [| discriminate H | discriminate H].
  exists f. 
  split. apply ext2_file_on_disk with (inodeIndex := inodeIndex). auto.
  split. apply verify_ext2_event2 with (disk := disk). auto.
  apply found_eq. auto.
Qed.


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
    rewrite <- H; apply verify_ext2_event3; vm_compute; reflexivity|]).

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
    | contradict Heqf; apply verify_ext2_event1; apply avoid_compute;
      vm_compute; eauto
    | contradict Heqf; apply verify_ext2_event1; apply avoid_compute;
      vm_compute; eauto].
  exists f.
  split. 
    (* isOnDisk *)
    apply ext2_file_on_disk in Heqf. apply Heqf.

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
      set (fileNames := parseFileNames (gunzip_a f)).
      vm_compute in fileNames.
      split. vm_compute. repeat (try (left; reflexivity); right).
      split. vm_compute. repeat (try (left; reflexivity); right).
      clear fileNames.
      split. vm_compute. repeat (try (left; reflexivity); right).
      split. vm_compute. repeat (try (left; reflexivity); right).
    vm_compute. intros contra. inversion contra.
Qed.
