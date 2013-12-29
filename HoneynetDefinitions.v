Require Import ByteData.
Require Import File.
Require Import FileData.
Require Import FileTypes.
Require Import Tar.

Open Local Scope bool.

Definition borland_evidence (disk: Disk) (unzip: File->File) :=
  exists f: File,
    isOnDisk f disk
    /\ isDeleted f
    /\ isGzip f disk
    /\ Tar.looksLikeRootkit (unzip f) disk.

Definition borland_compute (disk: Disk) (unzip: File->File)
  (file: File) (filename1 filename2: ByteString) :=
  (isOnDisk_comp file disk)
  && file.(deleted)
  && (isGzip_compute file disk)
  && Tar.looksLikeRootkit_compute (unzip file) disk filename1 filename2.

Lemma borland_reflection (disk: Disk) (unzip: File->File)
  (file: File) (filename1 filename2: ByteString) :
  borland_compute disk unzip file filename1 filename2 = true
    -> borland_evidence disk unzip.
Proof.
  intros. unfold borland_compute in H.
  apply Bool.andb_true_iff in H. destruct H.
  apply Bool.andb_true_iff in H. destruct H.
  apply Bool.andb_true_iff in H. destruct H.

  unfold borland_evidence. exists file.
  split. apply isOnDisk_reflection. auto.
  split. unfold isDeleted. auto.
  split. apply isGzip_reflection. auto.
  apply looksLikeRootkit_reflection in H0. auto.
Qed.
