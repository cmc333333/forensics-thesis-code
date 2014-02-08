Require Import Coq.Strings.String.

Require Import ByteData.
Require Import DiskSubset.
Require Import File.
Require Import FileData.
Require Import FileTypes.
Require Import Tar.

Variable gunzip: File->Disk->File.

Local Open Scope bool.

Definition borland_rootkit (disk: Disk) :=
  exists file: File,
    isOnDisk file disk
    /\ isDeleted file
    /\ isGzip file disk
    /\ Tar.looksLikeRootkit (gunzip file disk) disk.

Definition borland_rootkit_witness (disk: Disk) (file: File):=
  isOnDisk file disk
  /\ isDeleted file
  /\ isGzip file disk
  /\ Tar.looksLikeRootkit (gunzip file disk) disk.

Definition borland_rootkit_witness_param (disk: Disk) (file gunzipped: File):=
  isOnDisk file disk
  /\ isDeleted file
  /\ isGzip file disk
  /\ Tar.looksLikeRootkit gunzipped disk.


Lemma borland_rootkit_witness_impl :
  forall (file: File) (disk: Disk),
    borland_rootkit_witness disk file ->
      borland_rootkit disk.
Proof.
  intros file disk H.
  unfold borland_rootkit_witness in H.
  unfold borland_rootkit.
  exists file. assumption.
Qed.

Lemma borland_rootkit_fsubset :
  forall (gzippedFile gunzipped: File) (disk:Disk),
    gunzipped f⊆ (gunzip gzippedFile disk) ->
      borland_rootkit_witness_param disk gzippedFile gunzipped ->
        borland_rootkit_witness disk gzippedFile.
Proof.
  intros gzippedFile gunzipped disk subset H.
  unfold borland_rootkit_witness_param in H.
  unfold borland_rootkit_witness.
  destruct H as [H0 H]. destruct H as [H1 H]. destruct H as [H2 H].
  split. assumption.
  split. assumption.
  split. assumption.
  apply looksLikeRootkit_fsubset with (1:=subset).
  assumption.
Qed.


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
    -> (gunzip file disk) = gunzipped
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

Lemma borland_witness_param_reflection:
  forall (disk: Disk) (file gunzipped: File) (filename1 filename2: string),
    borland_compute disk file gunzipped filename1 filename2 = true ->
      borland_rootkit_witness_param disk file gunzipped.
Proof.
  intros. unfold borland_compute in H.
  apply Bool.andb_true_iff in H. destruct H.
  apply Bool.andb_true_iff in H. destruct H.
  apply Bool.andb_true_iff in H. destruct H.

  unfold borland_rootkit_witness_param.
  split. apply isOnDisk_reflection. auto.
  split. unfold isDeleted. auto.
  split. apply isGzip_reflection. auto.
         apply looksLikeRootkit_reflection in H0. auto.
Qed.

Lemma borland_rootkit_witness_subset:
  forall (sub super: Disk) (gzippedFile gunzipped: File),
    borland_rootkit_witness_param sub gzippedFile gunzipped ->
      sub ⊆ super ->
        gunzipped f⊆ (gunzip gzippedFile super) ->
            borland_rootkit super.
Proof.
  intros sub super gzippedFile gunzipped H subset fsubset.
  unfold borland_rootkit_witness_param in H.
  apply borland_rootkit_witness_impl with (file:=gzippedFile).
  unfold borland_rootkit_witness.
  destruct H as [HonDisk H]. destruct H as [Hdeleted H].
  destruct H as [Hgzip Hlooks].
  split. apply isOnDisk_subset with (1:=subset). assumption.
  split. assumption.
  split. apply isGzip_subset with (1:=subset). assumption.
         apply looksLikeRootkit_subset with (1:=subset) in Hlooks.
         apply looksLikeRootkit_fsubset with (1:=fsubset). assumption.
Qed.
