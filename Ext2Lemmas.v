Require Import Coq.ZArith.ZArith.

Require Import ByteData.
Require Import Ext2.
Require Import Fetch.
Require Import File.
Require Import FileData.
Require Import FileSystems.
Require Import Timeline.

Lemma ext2_avoid_compute:
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

Lemma findAndParseFile_ext2FS:
  forall (disk: Disk) (inodeIndex: Z) (file: File),
    findAndParseFile disk inodeIndex = Found file ->
      file.(fileSystem) = Ext2FS inodeIndex.
Proof.
  intros.
  unfold findAndParseFile in H.
  destruct (findAndParseSuperBlock disk); [ | discriminate H | discriminate H].
  simpl in H.
  destruct (findAndParseGroupDescriptor disk s 
              ((inodeIndex - 1) / inodesPerGroup s)); [
    | discriminate H | discriminate H]. simpl in H.
  destruct (findAndParseInode disk s g inodeIndex); [
    | discriminate H | discriminate H]. simpl in H.
  destruct (parseDeleted disk s g inodeIndex); [
    | discriminate H | discriminate H]. simpl in H.
  inversion H.
  reflexivity.
Qed.

Lemma ext2_file_on_disk: 
  forall (disk:Disk) (file:File) (inodeIndex:Z),
  Found file = findAndParseFile disk inodeIndex
  -> isOnDisk file disk.
Proof.
  intros.
  unfold isOnDisk. 
  assert (file.(fileSystem) = Ext2FS inodeIndex).
  apply findAndParseFile_ext2FS with (disk := disk).
  auto.
  rewrite H0. auto.
Qed.

Lemma ext2_field_match (X:Type):
  forall (fn: File->X) (x:X) (file:File) (disk:Disk) (inodeIndex:Z),
    (Found file = findAndParseFile disk inodeIndex
    /\ (findAndParseFile disk inodeIndex) _fmap_ (fn) = @Found X x)
    -> fn file = x.
Proof.
  intros. destruct H.
  apply wrap_with_found.
  rewrite <- H0. rewrite <- H. vm_compute. reflexivity.
Qed.

(*
Lemma ext2_byte_match:
  forall (byte offset inodeIndex: Z) (file:File) (disk:Disk),
    (Found file = findAndParseFile disk inodeIndex
    /\ (findAndParseFile disk inodeIndex) 
        _fflatmap_ (fun f => data f offset) = Found byte)
    -> data file offset = Found byte.
Proof.
  intros. destruct H.
  apply wrap_with_found.
  rewrite <- H0. rewrite <- H. vm_compute. reflexivity.
Qed.
*)

Lemma ext2_fetch_excl_middle (disk:Disk) (inodeIndex:Z): 
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

(*
Lemma inodeindex_is_fsid:
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
*)

Lemma verify_ext2_access:
  forall (disk: Disk) (inodeIndex: Z) (timestamp: Z),
    ((findAndParseFile disk inodeIndex) _fmap_ lastAccess 
      = (Found (Some timestamp))
    -> foundOn (FileAccess timestamp (Ext2FS inodeIndex)) disk).
Proof.
  intros. remember (findAndParseFile disk inodeIndex) as e.
  destruct e as [f Heq | z Heq | s Heq]; [| discriminate H | discriminate H].
  exists f. 
  split. apply ext2_file_on_disk with (inodeIndex := inodeIndex). auto.
  split. symmetry. apply findAndParseFile_ext2FS with (disk := disk). auto.
  apply wrap_with_found. auto.
Qed.

Lemma verify_ext2_modification:
  forall (disk: Disk) (inodeIndex: Z) (timestamp: Z),
    ((findAndParseFile disk inodeIndex) _fmap_ lastModification
      = (Found (Some timestamp))
    -> foundOn (FileModification timestamp (Ext2FS inodeIndex)) disk).
Proof.
  intros. remember (findAndParseFile disk inodeIndex) as e.
  destruct e as [f Heq | z Heq | s Heq]; [| discriminate H | discriminate H].
  exists f. 
  split. apply ext2_file_on_disk with (inodeIndex := inodeIndex). auto.
  split. symmetry. apply findAndParseFile_ext2FS with (disk := disk). auto.
  apply wrap_with_found. auto.
Qed.

Lemma verify_ext2_creation:
  forall (disk: Disk) (inodeIndex: Z) (timestamp: Z),
    ((findAndParseFile disk inodeIndex) _fmap_ lastCreated
      = (Found (Some timestamp))
    -> foundOn (FileCreation timestamp (Ext2FS inodeIndex)) disk).
Proof.
  intros. remember (findAndParseFile disk inodeIndex) as e.
  destruct e as [f Heq | z Heq | s Heq]; [| discriminate H | discriminate H].
  exists f. 
  split. apply ext2_file_on_disk with (inodeIndex := inodeIndex). auto.
  split. symmetry. apply findAndParseFile_ext2FS with (disk := disk). auto.
  apply wrap_with_found. auto.
Qed.

Lemma verify_ext2_deletion:
  forall (disk: Disk) (inodeIndex: Z) (timestamp: Z),
    ((findAndParseFile disk inodeIndex) _fmap_ lastDeleted
      = (Found (Some timestamp))
    -> foundOn (FileDeletion timestamp (Ext2FS inodeIndex)) disk).
Proof.
  intros. remember (findAndParseFile disk inodeIndex) as e.
  destruct e as [f Heq | z Heq | s Heq]; [| discriminate H | discriminate H].
  exists f. 
  split. apply ext2_file_on_disk with (inodeIndex := inodeIndex). auto.
  split. symmetry. apply findAndParseFile_ext2FS with (disk := disk). auto.
  apply wrap_with_found. auto.
Qed.
