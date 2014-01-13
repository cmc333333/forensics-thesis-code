(* positive negative examples for what doesn't work and what does; e.g. coqchk
*)


Require Import Coq.ZArith.ZArith.

Require Import ByteData.
Require Import File.
Require Import FileData.
Require Import FileIds.
Require Import Util.

Open Local Scope bool.
Open Local Scope N.

Inductive Event: Type :=
  | FileAccess: N -> FileId -> Event
  | FileModification: N -> FileId -> Event
  | FileCreation: N -> FileId -> Event
  | FileDeletion: N -> FileId -> Event
.

Definition eqb (lhs rhs: Event) :=
  match (lhs, rhs) with
  | (FileAccess l lfs, FileAccess r rfs) => 
      andb (FileIds.eqb lfs rfs) (N.eqb l r)
  | (FileModification l lfs, FileModification r rfs) => 
      andb (FileIds.eqb lfs rfs) (N.eqb l r)
  | (FileCreation l lfs, FileCreation r rfs) =>
      andb (FileIds.eqb lfs rfs) (N.eqb l r)
  | (FileDeletion l lfs, FileDeletion r rfs) =>
      andb (FileIds.eqb lfs rfs) (N.eqb l r)
  | _ => false
  end.

Definition Timeline: Type := list Event.

Definition timestampOf (event: Event) : Exc N :=
  match event with
  | FileAccess timestamp _ => value timestamp
  | FileModification timestamp _ => value timestamp
  | FileCreation timestamp _ => value timestamp
  | FileDeletion timestamp _ => value timestamp
  end.

Definition beforeOrConcurrent (lhs rhs: Event) :=
  match (timestampOf lhs, timestampOf rhs) with
  | (value lhs_time, value rhs_time) => lhs_time <=? rhs_time
  | _ => false
  end.

Definition foundOn (event: Event) (disk: Disk) :=
  match event with
  | FileAccess timestamp fs => exists (file: File),
        isOnDisk file disk
        /\ fs = file.(fileId)
        /\ file.(lastAccess) = value timestamp
  | FileModification timestamp fs => exists (file: File),
        isOnDisk file disk
        /\ fs = file.(fileId)
        /\ file.(lastModification) = value timestamp
  | FileCreation timestamp fs => exists (file: File),
        isOnDisk file disk
        /\ fs = file.(fileId)
        /\ file.(lastCreated) = value timestamp
  | FileDeletion timestamp fs => exists (file: File),
        isOnDisk file disk
        /\ fs = file.(fileId)
        /\ file.(lastDeleted) = value timestamp
  end.

Definition foundOn_compute (event: Event) (disk: Disk) (file: File) :=
  match event with
  | FileAccess timestamp fs => 
    isOnDisk_compute file disk
    && FileIds.eqb fs file.(fileId)
    && optN_eqb file.(lastAccess) (value timestamp)
  | FileModification timestamp fs =>
    isOnDisk_compute file disk
    && FileIds.eqb fs file.(fileId)
    && optN_eqb file.(lastModification) (value timestamp)
  | FileCreation timestamp fs =>
    isOnDisk_compute file disk
    && FileIds.eqb fs file.(fileId)
    && optN_eqb file.(lastCreated) (value timestamp)
  | FileDeletion timestamp fs =>
    isOnDisk_compute file disk
    && FileIds.eqb fs file.(fileId)
    && optN_eqb file.(lastDeleted) (value timestamp)
  end.

Lemma foundOn_reflection (event: Event) (disk: Disk) (file: File) :
  foundOn_compute event disk file = true -> foundOn event disk.
Proof.
  intros. 
  unfold foundOn_compute in H.  unfold foundOn.
  destruct event.
    apply Bool.andb_true_iff in H; destruct H;
      apply Bool.andb_true_iff in H; destruct H;
      exists file;
        split; 
          [ apply isOnDisk_reflection; auto
          | split; 
            [ apply FileIds.eqb_reflection; auto
            | apply optN_eqb_reflection; auto]].
    apply Bool.andb_true_iff in H; destruct H;
      apply Bool.andb_true_iff in H; destruct H;
      exists file;
        split; 
          [ apply isOnDisk_reflection; auto
          | split; 
            [ apply FileIds.eqb_reflection; auto
            | apply optN_eqb_reflection; auto]].
    apply Bool.andb_true_iff in H; destruct H;
      apply Bool.andb_true_iff in H; destruct H;
      exists file;
        split; 
          [ apply isOnDisk_reflection; auto
          | split; 
            [ apply FileIds.eqb_reflection; auto
            | apply optN_eqb_reflection; auto]].
    apply Bool.andb_true_iff in H; destruct H;
      apply Bool.andb_true_iff in H; destruct H;
      exists file;
        split; 
          [ apply isOnDisk_reflection; auto
          | split; 
            [ apply FileIds.eqb_reflection; auto
            | apply optN_eqb_reflection; auto]].
Qed. 

Definition isSoundPair (disk: Disk) (eventPair: Event*Event) :=
  let (lhsEvent, rhsEvent) := eventPair in
  foundOn lhsEvent disk
  /\ foundOn rhsEvent disk
  /\ beforeOrConcurrent lhsEvent rhsEvent = true.

Definition isSoundPair_compute (disk: Disk) 
  (pairPair: (Event*Event)*(File*File)) :=
  let (eventPair, filePair) := pairPair in
  let (lhsEvent, rhsEvent) := eventPair in
  let (lhsFile, rhsFile) := filePair in
  foundOn_compute lhsEvent disk lhsFile
  && foundOn_compute rhsEvent disk rhsFile
  && beforeOrConcurrent lhsEvent rhsEvent.

Lemma isSoundPair_reflection (disk: Disk)
  (eventPair: Event*Event) (filePair: File*File) :
  isSoundPair_compute disk (eventPair, filePair) = true ->
    isSoundPair disk eventPair.
Proof.
  intros. 
    destruct eventPair as [lhsEvent rhsEvent].
    destruct filePair as [lhsFile rhsFile].
  
  unfold isSoundPair_compute in H.
  unfold isSoundPair.
  apply Bool.andb_true_iff in H. destruct H. 
  apply Bool.andb_true_iff in H. destruct H. 
  split. 
    apply foundOn_reflection with (file := lhsFile). auto.
  split. 
    apply foundOn_reflection with (file := rhsFile). auto.

    auto.
Qed.

Definition isSound (timeline: Timeline) (disk: Disk) :=
  let staggeredEvents := combine timeline (skipn 1 timeline) in
  forall (pair: Event*Event),
    In pair staggeredEvents -> isSoundPair disk pair.

Definition isSound_tmp (timeline: Timeline) (disk: Disk) :=
  exists (files: list File),
    let staggeredEvents := combine timeline (skipn 1 timeline) in
    let staggeredFiles := combine files (skipn 1 files) in
    let combined := combine staggeredEvents staggeredFiles in
    length staggeredEvents = length staggeredFiles
    /\ forall (pairPair: (Event*Event)*(File*File)),
        In pairPair combined -> isSoundPair disk (fst pairPair).

Lemma strip_list_l {L R: Type} (lhs:list L) (rhs: list R)
  (prop:L->Prop) : 
  length lhs = length rhs
  -> (forall (pair: L*R), In pair (combine lhs rhs) -> prop (fst pair))
  -> (forall (l: L), In l lhs -> prop l).
Proof.
  generalize rhs prop. clear rhs prop.
  induction lhs. 
    intros. destruct rhs; [
      contradict H1
      | simpl in H; discriminate H].
    intros. destruct rhs; [ 
      simpl in H; discriminate H
      |]. 
      destruct H1.
        specialize (H0 (l, r)).
          simpl in H0. apply H0. left. subst. reflexivity.
        apply IHlhs with (rhs := rhs).
          inversion H. reflexivity.
          intros pair inn.
            assert (In pair (combine (a :: lhs) (r :: rhs))).
            apply in_cons. assumption.
          apply H0. assumption.
          assumption.
Qed.

Lemma isSound_tmp_impl (timeline: Timeline) (disk: Disk) :
  isSound_tmp timeline disk -> isSound timeline disk.
Proof.
  intros.
    unfold isSound_tmp in H. destruct H as [files]. destruct H.
    unfold isSound.
    remember (combine timeline (skipn 1 timeline)) as staggeredEvents.
    remember (combine files (skipn 1 files)) as staggeredFiles.
    apply strip_list_l with (rhs := staggeredFiles).
    assumption. assumption.
Qed.

Definition isSound_compute (timeline: Timeline) (disk: Disk) 
  (files: list File) :=
  let staggeredEvents := combine timeline (skipn 1 timeline) in
  let staggeredFiles := combine files (skipn 1 files) in
  let combined := combine staggeredEvents staggeredFiles in
  beq_nat (length staggeredEvents) (length staggeredFiles)
  && forallb (isSoundPair_compute disk) combined.

Lemma isSound_reflection (timeline: Timeline) (disk: Disk)
  (files: list File) :
  isSound_compute timeline disk files = true ->
    isSound timeline disk.
Proof.
  intros. apply isSound_tmp_impl. unfold isSound_tmp. exists files.
  unfold isSound_compute in H.
  apply Bool.andb_true_iff in H. destruct H. 
  split. apply beq_nat_eq. auto.
  rewrite forallb_forall in H0.
  intros. apply isSoundPair_reflection with (filePair := snd pairPair).
  assert (fst pairPair |-> snd pairPair = pairPair).
    destruct pairPair. simpl. reflexivity.
  rewrite H2.
  auto.
Qed.
