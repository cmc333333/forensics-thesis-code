Require Import Coq.ZArith.ZArith.

Require Import ByteData.
Require Import Ext2.
Require Import Fetch.
Require Import FileSystems.
Require Import File.

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

Lemma verify_ext2_event {T: Type}:
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
  split. apply inodeindex_is_fsid with (disk := disk). auto.
  apply wrap_with_found. auto.
Qed.
