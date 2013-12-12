(* How much effort is it to prove that a file exists,
   Either type with error/none/success,
   Basic Category Theory *)

(* Try to convert all of the tactics into definitions *)

Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Evm_compute.

Require Import ByteData.
Require Import Ext2.
(*Require Import Ext2Lemmas.*)
Require Import Fetch.
Require Import File.
Require Import FileNames.
Require Import FileSystems.
Require Import FileTypes.
Require Import Tar.
(*Require Import Timeline.*)
Require Import Util.

Require Import example_images.

Open Local Scope Z.

Definition honeynet_image_a : Disk := honeynet_map.
(* All gunzip operations return the file mentioned *)
Definition gunzip_a := (fun (input: File) => 
  let asDisk := Disk_of_Map_Z_Z gunzipped_23 in
  (mkFile (FileSystems.MockFS asDisk)
          1454080 (* uncompressed file size *)
          input.(deleted) 
          (* Fields not used; ignore them *)
          None None None None)).



(*
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
    rewrite <- H; apply verify_ext2_event; vm_compute; reflexivity|]).

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
*)

Lemma bar2 : 
  forall (A B : Type) (f : A -> B) (x : A) (y : B) (z : @Fetch A), 
    (match z with
      | Found v => Found (f v)
      | ErrorString str => ErrorString str
      | MissingAt pos => MissingAt pos
    end = Found y) ->
    z = Found x ->
    f x = y.
Proof.
  intros A B f x y z Hsome Hf.
  destruct z; [
    injection Hsome; intros; subst;
      injection Hf; intros; subst;
        reflexivity
    | discriminate Hf
    | discriminate Hf
  ].
Qed.

Lemma borland_honeynet_file:
  exists f: File,
  Found f = (findAndParseFile honeynet_image_a 23)
  /\ isDeleted f
  /\ isGzip f honeynet_image_a
  /\ Tar.looksLikeRootkit (gunzip_a f) honeynet_image_a.
  Proof.
    exists (mkFile (Ext2FS 23)
                   520333
                   true
                   (Some 984707090)
                   (Some 984706608)
                   (Some 984707105)
                   (Some 984707105)).
    split. vm_compute. reflexivity.
    split. reflexivity.
    split. vm_compute. repeat (split ; [reflexivity| ]); reflexivity.
    unfold looksLikeRootkit.
    exists (ascii2Bytes "last/ssh"); exists (ascii2Bytes "last/top").
    unfold gunzip_a. simpl parseFileNames.

    split. vm_compute. reflexivity.
    split. vm_compute. reflexivity.
    split. vm_compute. repeat (try (left; reflexivity); right).
    split. vm_compute. repeat (try (left; reflexivity); right).
    vm_compute. reflexivity.
    Show Proof.
Qed.
