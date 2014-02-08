Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Require Import Byte.
Require Import ByteData.
Require Import DiskSubset.
Require Import Fetch.
Require Import File.
Require Import FileData.
Require Import FileIds.
Require Import FileNames.
Require Import StringOps.
Require Import Util.

Local Open Scope bool.
Local Open Scope N.

Fixpoint fromOctalAscii (bytes: list Byte) : Exc N :=
  match bytes with
  | nil => value 0
  | byte :: tl => match (fromOctalAscii tl) with
    | error => error
    | value rest => 
      let byte := Ascii.N_of_ascii byte in
      if (andb (48 <=? byte) (byte <=? 56))
      then value (rest + ((byte - 48) 
                          * (8 ^ (N.of_nat (List.length tl)))))
      else error (* Invalid character *)
    end
  end.

Definition parseFileName (tar: File) (offset: N) (disk: Disk): @Fetch string :=
  N.peano_rect
  (fun _ => N -> @Fetch string) (* Signature of recursive calls *)
  (fun (_: N) => Found EmptyString) (* Base case -- empty file *)
  (fun (prev: N) (rec: N -> @Fetch string) (idx: N) =>
    (* Recursive case -- more file remaining *)
    match (tar @[ offset + idx | disk ]) with
    | Found byte => 
      if (ascii_eqb byte Ascii.zero) (* Null *)
      then Found EmptyString
      else match (rec (idx + 1)) with
      | Found rest => Found (String byte rest)
      | MissingAt val => MissingAt val
      | ErrorString val => ErrorString val
      end
    | MissingAt val => MissingAt val
    | ErrorString val => ErrorString val
    end)
  100 0.

Lemma parseFileName_subset:
  forall (sub super: Disk) (tar: File) (offset: N) (val: string),
    sub ⊆ super ->
      parseFileName tar offset sub = Found val ->
        parseFileName tar offset super = Found val.
Proof.
  unfold parseFileName.
  generalize 0.
  apply N.peano_ind with (n := 100).
    simpl; auto.
  intros n H m sub super tar offset val subset H1.
  rewrite N.peano_rect_succ.
  rewrite N.peano_rect_succ in H1.
  destruct (tar @[ offset + m | sub ]) eqn:TarAt;
      [| discriminate H1 | discriminate H1].
  apply fetchByte_subset with (1:=subset) in TarAt.
  rewrite TarAt. 
  destruct (ascii_eqb b zero) eqn:IsZero.
  assumption.
  match goal with   (* match helps us reference subterms in the goal *)
    | [ _: match ?peano with _ => _ end = _ |- _] => 
        destruct peano eqn:Hpeano; [| discriminate H1 | discriminate H1]
  end.
  apply H with (1:=subset) in Hpeano. rewrite Hpeano. 
  assumption.
Qed.


Definition parseFileSize (tar: File) (offset: N) (disk: Disk): @Fetch N :=
  (tar @[ offset + 124 | disk ]) _fflatmap_ (fun byte0 =>
  (tar @[ offset + 125 | disk ]) _fflatmap_ (fun byte1 =>
  (tar @[ offset + 126 | disk ]) _fflatmap_ (fun byte2 =>
  (tar @[ offset + 127 | disk ]) _fflatmap_ (fun byte3 =>
  (tar @[ offset + 128 | disk ]) _fflatmap_ (fun byte4 =>
  (tar @[ offset + 129 | disk ]) _fflatmap_ (fun byte5 =>
  (tar @[ offset + 130 | disk ]) _fflatmap_ (fun byte6 =>
  (tar @[ offset + 131 | disk ]) _fflatmap_ (fun byte7 =>
  (tar @[ offset + 132 | disk ]) _fflatmap_ (fun byte8 =>
  (tar @[ offset + 133 | disk ]) _fflatmap_ (fun byte9 =>
  (tar @[ offset + 134 | disk ]) _fflatmap_ (fun byte10 =>
    match (fromOctalAscii (byte0 :: byte1 :: byte2 :: byte3
                           :: byte4 :: byte5 :: byte6 :: byte7
                           :: byte8 :: byte9 :: byte10 :: nil)) with
    | error => 
        if ((Byte.eqb byte0 Ascii.zero) && (Byte.eqb byte1 Ascii.zero)
            && (Byte.eqb byte2 Ascii.zero) && (Byte.eqb byte3 Ascii.zero)
            && (Byte.eqb byte4 Ascii.zero) && (Byte.eqb byte5 Ascii.zero)
            && (Byte.eqb byte6 Ascii.zero) && (Byte.eqb byte7 Ascii.zero)
            && (Byte.eqb byte8 Ascii.zero) && (Byte.eqb byte9 Ascii.zero)
            && (Byte.eqb byte10 Ascii.zero))
          (* the last few chunks of the Tar file are full of zeros *)
          then Found 0
          (* something went wrong *)
          else ErrorString "Invalid Tar Size"
    | value size => Found size
    end))))))))))).

Lemma parseFileSize_subset:
  forall (sub super: Disk) (tar: File) (offset: N) (val: N),
    sub ⊆ super ->
      parseFileSize tar offset sub = Found val ->
        parseFileSize tar offset super = Found val.
Proof.
  intros sub super tar offset val subset.
  unfold parseFileSize.
  unfold disk_subset in subset.
  repeat (apply found_fflatmap_found_twice; [
    intros ?; apply fetchByte_subset with (1:=subset)
    | intro; intro]).
  intros. assumption.
Qed.


Definition parseFileNameAndSize (tar: File) (offset: N) 
  (disk: Disk) : @Fetch (string*N) :=
  (parseFileName tar offset disk) _fflatmap_ (fun name =>
  (parseFileSize tar offset disk) _fmap_ (fun size =>
    (name, size)
  )).

Lemma parseFileNameAndSize_subset:
  forall (sub super: Disk) (tar: File) (offset: N) (val: string*N),
    sub ⊆ super ->
      parseFileNameAndSize tar offset sub = Found val ->
        parseFileNameAndSize tar offset super = Found val.
Proof.
  intros sub super tar offset val subset.
  unfold parseFileNameAndSize.
  intros H.
  apply found_fflatmap_found in H. destruct H as [fileName [HfileName H]].
  apply found_fmap_found in H. destruct H as [size [Hsize H]].
  apply parseFileName_subset with (1:=subset) in HfileName.
  rewrite HfileName. unfold fetch_flatmap at 1.
  apply parseFileSize_subset with (1:=subset) in Hsize.
  rewrite Hsize. unfold fetch_map at 1.
  rewrite H. auto.
Qed.


Definition recFileNameFrom (nextCall: N -> @Fetch (list string))
  (tar: File) (offset: N) (disk: Disk) : @Fetch (list string) :=
  if (tar.(fileSize) <=? offset)
    then Found nil
  else match 
    (parseFileNameAndSize tar offset disk) with
    | Found (fileName, fileSize) =>
        (* Strip the next file out of the tar *)
        (* Round to the nearest 512 *)
        let nextFileSize := (
          if (fileSize mod 512 =? 0)
          then fileSize + 512
          else 512 * (2 + (fileSize / 512))) in
        match (nextCall (offset + nextFileSize)) with
        | Found rest => Found (fileName :: rest)
        | MissingAt val => MissingAt val
        | ErrorString val => ErrorString val
        end
    | MissingAt val => MissingAt val
    | ErrorString val => ErrorString val
    end.

Definition parseFileNames (file: File) (disk: Disk): @Fetch (list string) :=
  N.peano_rect
  (fun _ => N -> @Fetch (list string)) (* Signature of recursive calls *)
  (fun (_: N) => Found (nil:(list string))) (* Base case -- empty file *)
  (fun (prev: N) (rec: N -> @Fetch (list string)) (offset: N) =>
    (* Recursive case -- more file remaining *)
    recFileNameFrom rec file offset disk)  
  file.(fileSize)
  0.

Lemma parseFileNames_subset:
  forall (sub super: Disk) (file: File) (val: list string),
    sub ⊆ super ->
      parseFileNames file sub = Found val ->
        parseFileNames file super = Found val.
Proof.
  unfold parseFileNames. 
  intros sub super file. revert sub super.
  generalize 0.
  apply N.peano_ind with (n := fileSize file).
    simpl; auto.
  intros n H m sub super val subset H1.
  rewrite N.peano_rect_succ.
  rewrite N.peano_rect_succ in H1.
  unfold recFileNameFrom at 1.
  unfold recFileNameFrom at 1 in H1.
  destruct (fileSize file <=? m) eqn:H_fileSize.
    assumption.
  destruct (parseFileNameAndSize file m sub) eqn:H_fileNameAndSize;
    [| discriminate H1 | discriminate H1].
  destruct p as [fileName fileSize]. 
  apply parseFileNameAndSize_subset with (1:=subset) in H_fileNameAndSize.
  rewrite H_fileNameAndSize.
  destruct (fileSize mod 512 =? 0) eqn:H_fsize_mod_512.
  simpl. simpl in H1.
  match goal with   (* match helps us reference subterms in the goal *)
    | [ _: match ?peano with _ => _ end = _ |- _] => 
        destruct peano eqn:Hpeano; [| discriminate H1 | discriminate H1]
  end.
  apply H with (1:=subset) in Hpeano. rewrite Hpeano.
  assumption.
  cbv zeta. cbv zeta in H1.
  destruct (N.peano_rect (fun _ : N => N -> Fetch) (fun _ : N => Found nil)
                         (fun (_ : N) (rec : N -> Fetch) (offset : N) =>
                         recFileNameFrom rec file offset sub) n
                         (m + 512 * (2 + fileSize / 512))) eqn:Hpeano;
    [|discriminate H1 | discriminate H1].
  apply H with (1:=subset) in Hpeano. rewrite Hpeano.
  assumption.
Qed.

Definition looksLikeRootkit (file: File) (disk: Disk) :=
  match (parseFileNames file disk) with
  | Found fileNames =>
    exists (filename1 filename2: string),
      filename1 <> filename2
      /\ In filename1 fileNames
      /\ In filename2 fileNames
      /\ (FileNames.systemFile filename1)
      /\ (FileNames.systemFile filename2)
  | _ => False
  end.

Definition looksLikeRootkit_compute (file: File) (disk: Disk)
  (filename1 filename2: string) :=
  match (parseFileNames file disk) with
  | Found fileNames =>
       (negb (string_eqb filename1 filename2))
    && (existsb (string_eqb filename1) fileNames)
    && (existsb (string_eqb filename2) fileNames)
    && (FileNames.systemFile_compute filename1)
    && (FileNames.systemFile_compute filename2)
  | _ => false
  end.

Lemma looksLikeRootkit_reflection (file: File) (disk: Disk)
  (filename1 filename2: string) :
  looksLikeRootkit_compute file disk filename1 filename2 = true
    -> looksLikeRootkit file disk.
Proof.
  intros. unfold looksLikeRootkit_compute in H. 
  unfold looksLikeRootkit.
  destruct (parseFileNames file disk); [|discriminate H | discriminate].
  apply Bool.andb_true_iff in H. destruct H.
  apply Bool.andb_true_iff in H. destruct H.
  apply Bool.andb_true_iff in H. destruct H.
  apply Bool.andb_true_iff in H. destruct H.
  exists filename1. exists filename2.
  split. 
    compute. intros. apply <- string_eqb_reflection in H4.
    rewrite H4 in H. discriminate H.
  split.
    apply existsb_exists in H3. destruct H3. destruct H3.
    apply string_eqb_reflection in H4. rewrite <- H4 in H3. auto.
  split. 
    apply existsb_exists in H2. destruct H2. destruct H2.
    apply string_eqb_reflection in H4. rewrite <- H4 in H2. auto.
  split. 
    apply systemFile_reflection. auto.

    apply systemFile_reflection. auto.
Qed.

Lemma looksLikeRootkit_subset:
  forall (sub super: Disk) (file: File),
    sub ⊆ super ->
      looksLikeRootkit file sub ->
        looksLikeRootkit file super.
Proof.
  intros sub super file subset.
  unfold looksLikeRootkit.
  intros H.
  destruct (parseFileNames file sub) eqn:H_parseFileNames.
    apply parseFileNames_subset with (1:=subset) in H_parseFileNames.
    rewrite H_parseFileNames. assumption.
  contradict H.
  contradict H.
Qed.
