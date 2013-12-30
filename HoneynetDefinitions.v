Require Import ByteData.
Require Import File.
Require Import FileData.
Require Import FileTypes.
Require Import Tar.

Open Local Scope bool.

Definition borland_rootkit (disk: Disk) (gunzip: File->File) :=
  exists file: File,
    isOnDisk file disk
    /\ isDeleted file
    /\ isGzip file disk
    /\ Tar.looksLikeRootkit (gunzip file) disk.

Definition borland_compute (disk: Disk) (gunzip: File->File)
  (file: File) (filename1 filename2: ByteString) :=
  (isOnDisk_compute file disk)
  && file.(deleted)
  && (isGzip_compute file disk)
  && Tar.looksLikeRootkit_compute (gunzip file) disk filename1 filename2.

Lemma borland_reflection (disk: Disk) (gunzip: File->File)
  (file: File) (filename1 filename2: ByteString) :
  borland_compute disk gunzip file filename1 filename2 = true
    -> borland_rootkit disk gunzip.
Proof.
  intros. unfold borland_compute in H.
  apply Bool.andb_true_iff in H. destruct H.
  apply Bool.andb_true_iff in H. destruct H.
  apply Bool.andb_true_iff in H. destruct H.

  unfold borland_rootkit. exists file.
  split. apply isOnDisk_reflection. auto.
  split. unfold isDeleted. auto.
  split. apply isGzip_reflection. auto.
  apply looksLikeRootkit_reflection in H0. auto.
Qed.
