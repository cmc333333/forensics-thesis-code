Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Require Import Byte.
Require Import ByteData.
Require Import Fetch.
Require Import File.
Require Import FileData.
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

Definition parseFileName (bytes: ByteData) :=
  let firstHundredBytes := map bytes (0 upto 100) in
  let perByte := fun (acc: @Fetch (list Byte) )
                     (next: @Fetch Byte) =>
    match (acc, next) with
    | (Found (hd :: tl), Found next) =>
        if (ascii_eqb hd Ascii.zero)  (* Null *)
        then acc
        else Found (next :: hd :: tl)
    | (Found _, Found next) =>
        Found (next :: nil)
    | (Found (hd :: tl), MissingAt idx) =>
        if (ascii_eqb hd Ascii.zero)  (* Null *)
        then acc
        else MissingAt idx
    | (Found (hd :: tl), ErrorString str) =>
        if (ascii_eqb hd Ascii.zero)  (* Null *)
        then acc
        else ErrorString str
    | (other, _) => other
    end in
  (fold_left perByte firstHundredBytes (Found nil)) 
    _fmap_ (fun byteList => match byteList with
    (* Strip off the null character *)
    | hd :: tl => list2string (rev tl)
    | _ => EmptyString
    end).

Definition parseFileSize (bytes: ByteData) :=
  (seq_list bytes 124 11)
    _fflatmap_ (fun fileSizeList =>
    match (fromOctalAscii fileSizeList) with
    | error => ErrorString "Invalid Tar Size"
    | value size => Found size
    end).

Definition parseFileNameAndSize (tar: File) (offset: N) 
  (disk: Disk)
  : @Fetch (string*N) :=
  let byteData := shift (fetchByte tar.(fileId) disk) 
                        offset in
  (parseFileName byteData) _fflatmap_ (fun name =>
  (parseFileSize byteData) _fmap_ (fun size =>
    (name, size)
  )).

Definition recFileNameFrom (nextCall: N -> list string) 
  (tar: File) (remaining: N) (disk: Disk) : list string :=
  if (remaining <=? 0)
    then nil
  else match 
    (parseFileNameAndSize tar
                          (tar.(fileSize) - remaining) 
                          disk) with
    | Found (fileName, fileSize) =>
        (* Strip the next file out of the tar *)
        (* Round to the nearest 512 *)
        let nextFileSize := (
          if (fileSize mod 512 =? 0)
          then fileSize + 512
          else 512 * (2 + (fileSize / 512))) in
        fileName :: (nextCall (remaining - nextFileSize))
    | _ => nil
    end.

Definition parseFileNames (file: File) (disk: Disk): list string :=
  N.peano_rect
  (fun _ => N -> list string) (* Signature of recursive calls *)
  (fun (_: N) => nil:(list string)) (* Base case -- empty file *)
  (fun (prev: N) (rec: N -> list string) (remaining: N) =>
    (* Recursive case -- more file remaining *)
    recFileNameFrom rec file remaining disk)  
  file.(fileSize)
  file.(fileSize).

Definition looksLikeRootkit (file: File) (disk: Disk) :=
  let fileNames := parseFileNames file disk in
  exists (filename1 filename2: string),
    filename1 <> filename2
    /\ In filename1 fileNames
    /\ In filename2 fileNames
    /\ (FileNames.systemFile filename1)
    /\ (FileNames.systemFile filename2).

Definition looksLikeRootkit_compute (file: File) (disk: Disk)
  (filename1 filename2: string) :=
  let fileNames := parseFileNames file disk in
     (negb (string_eqb filename1 filename2))
  && (existsb (string_eqb filename1) fileNames)
  && (existsb (string_eqb filename2) fileNames)
  && (FileNames.systemFile_compute filename1)
  && (FileNames.systemFile_compute filename2).

Lemma looksLikeRootkit_reflection (file: File) (disk: Disk)
  (filename1 filename2: string) :
  looksLikeRootkit_compute file disk filename1 filename2 = true
    -> looksLikeRootkit file disk.
Proof.
  intros. unfold looksLikeRootkit_compute in H. 
  unfold looksLikeRootkit.
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
