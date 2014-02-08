Require Import Coq.Strings.String.

Require Import ByteData.
Require Import DiskSubset.
Require Import File.
Require Import FileData.
Require Import FileTypes.
Require Import Tar.

Variable gunzip: File->File.

Local Open Scope bool.

Definition borland_rootkit (disk: Disk) :=
  exists file: File,
    isOnDisk file disk
    /\ isDeleted file
    /\ isGzip file disk
    /\ Tar.looksLikeRootkit (gunzip file) disk.

Definition borland_compute (disk: Disk) (file gunzipped: File)
  (filename1 filename2: string) :=
  (isOnDisk_compute file disk)
  && file.(deleted)
  && (isGzip_compute file disk)
  (*&& File.eqb gunzipped (gunzip file) *)
  && Tar.looksLikeRootkit_compute gunzipped disk filename1 filename2.

Lemma borland_reflection (disk: Disk) 
  (file gunzipped: File) (filename1 filename2: string) :
  borland_compute disk file gunzipped filename1 filename2 = true
    -> (gunzip file) = gunzipped
      -> borland_rootkit disk.
Proof.
  intros. unfold borland_compute in H.
  apply Bool.andb_true_iff in H. destruct H.
  apply Bool.andb_true_iff in H. destruct H.
  apply Bool.andb_true_iff in H. destruct H.

  unfold borland_rootkit. exists file.
  split. apply isOnDisk_reflection. auto.
  split. unfold isDeleted. auto.
  split. apply isGzip_reflection. auto.
  rewrite H0. apply looksLikeRootkit_reflection in H1. auto.
Qed.

Lemma borland_rootkit_subset:
  forall (sub super: Disk),
    sub ⊆ super ->
      borland_rootkit sub ->
        borland_rootkit super.
Proof.
  intros sub super subset.
  unfold borland_rootkit.
  intros H.
  destruct H as [file H]. exists file.
  destruct H. destruct H0. destruct H1.
  split. apply isOnDisk_subset with (1:=subset). assumption.
  split. assumption.
  split. apply isGzip_subset with (1:=subset). assumption.
         apply looksLikeRootkit_subset with (1:=subset). assumption.
Qed.
