Require Import Coq.ZArith.ZArith.

Require Import ByteData.
Require Import File.
Require Import FileData.
Require Import FileSystems.
Require Import Util.

Open Local Scope Z.

Inductive Event: Type :=
  | FileAccess: Z -> FileSystem -> Event
  | FileModification: Z -> FileSystem -> Event
  | FileCreation: Z -> FileSystem -> Event
  | FileDeletion: Z -> FileSystem -> Event
.

Definition eqb (lhs rhs: Event) :=
  match (lhs, rhs) with
  | (FileAccess l lfs, FileAccess r rfs) => 
      andb (FileSystems.eqb lfs rfs) (Z.eqb l r)
  | (FileModification l lfs, FileModification r rfs) => 
      andb (FileSystems.eqb lfs rfs) (Z.eqb l r)
  | (FileCreation l lfs, FileCreation r rfs) =>
      andb (FileSystems.eqb lfs rfs) (Z.eqb l r)
  | (FileDeletion l lfs, FileDeletion r rfs) =>
      andb (FileSystems.eqb lfs rfs) (Z.eqb l r)
  | _ => false
  end.

Definition Timeline: Type := list Event.

Definition timestampOf (event: Event) : Exc Z :=
  match event with
  | FileAccess timestamp _ => value timestamp
  | FileModification timestamp _ => value timestamp
  | FileCreation timestamp _ => value timestamp
  | FileDeletion timestamp _ => value timestamp
  end.

Definition beforeOrConcurrent (lhs rhs: Event) :=
  match (timestampOf lhs, timestampOf rhs) with
  | (value lhs_time, value rhs_time) => lhs_time <= rhs_time
  | _ => False
  end.

Definition foundOn (event: Event) (disk: Disk) : Prop :=
  exists (file: File),
    isOnDisk file disk
    /\ match event with
       | FileAccess timestamp fs =>
          fs = file.(fileSystem) /\ file.(lastAccess) = value timestamp
       | FileModification timestamp fs =>
          fs = file.(fileSystem) /\ file.(lastModification) = value timestamp
       | FileCreation timestamp fs =>
          fs = file.(fileSystem) /\ file.(lastCreated) = value timestamp
       | FileDeletion timestamp fs =>
          fs = file.(fileSystem) /\ file.(lastDeleted) = value timestamp
       end.

Definition isInOrder (timeline: Timeline) :=
  (* Events are in the correct sequence *)
  let firstEvents := firstn (length timeline - 1) timeline in
  let secondEvents := skipn 1 timeline in
  let pairs := combine firstEvents secondEvents in
  forall (pair: (Event*Event)),
    In pair pairs -> beforeOrConcurrent (fst pair) (snd pair).

Definition isSound (timeline: Timeline) (disk: Disk) :=
  let pairs := combine timeline (skipn 1 timeline) in
  forall (pair: (Event*Event)),
    In pair pairs -> 
      (foundOn (fst pair) disk)
      /\ (foundOn (snd pair) disk)
      /\ beforeOrConcurrent (fst pair) (snd pair).
(*
  (forall (event: Event),
    (* Event is evident from the disk *)
    (In event timeline) -> (foundOn event disk))
  /\ isInOrder timeline.
*)
