Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Require Import ByteData.
Require Import Fetch.
Require Import File.
Require Import FileData.
Require Import FileNames.
Require Import StringOps.
Require Import Util.

Local Open Scope bool.
Local Open Scope Z.

Fixpoint fromOctalAscii (bytes: list Z) : Exc Z :=
  match bytes with
  | nil => value 0
  | byte :: tail => match (fromOctalAscii tail) with
    | error => error
    | value rest => if (andb (48 <=? byte) (byte <=? 56))
      then value (rest + ((byte-48) 
                          * (8 ^ (Z.of_nat (List.length tail)))))
      else error (* Invalid character *)
    end
  end.

Fixpoint listZ2string (str: list Z) :=
  match str with
  | nil => EmptyString
  | char :: rest => String (Ascii.ascii_of_N (Z.to_N char))
                           (listZ2string rest)
  end.

Definition parseFirstFileNameAndSize (tar: File) (offset: Z) (disk: Disk)
  : @Fetch (string*Z) :=
  let firstHundredBytes := map (fetchByte tar disk) 
                               (offset upto (100 + offset)) in
  let fileNameZ := fetch_flatten (takeWhile 
    (fun (byte: @Fetch Z) => match byte with
      | Found 0 => false (* stop *)
      | Found _ => true  (* continue *)
      | _ => false       (* stop *)
    end) firstHundredBytes) in
  let fileName := listZ2string fileNameZ in
  (* File Size is encoded in octal, represented as ASCII characters. It begins
  at offset 124 and runs for 11 characters *)
  (seq_list (fetchByte tar disk) (offset + 124) 11) 
    _fflatmap_ (fun fileSizeList =>
  match (fromOctalAscii fileSizeList) _map_ (fun fileSize =>
    (fileName, fileSize)
  ) with 
  | error => ErrorString "Invalid Tar File Size"
  | value v => Found v
  end).

Definition recFileNameFrom (nextCall: Z -> list string) 
  (tar: File) (remaining: Z) (disk: Disk) : list string :=
  if (remaining <=? 0)
    then nil
  else match (parseFirstFileNameAndSize tar (tar.(fileSize) - remaining) disk) with
    | Found (fileName, firstSize) =>
        (* Strip the first file out of the tar *)
        (* Round to the nearest 512 *)
        let firstFileSize := (
          if (firstSize mod 512 =? 0)
          then firstSize + 512
          else 512 * (2 + (firstSize / 512))) in

        fileName :: (nextCall (remaining - firstFileSize))
    | _ => nil
    end.

Definition parseFileNames (file: File) (disk: Disk): list string :=
  N.peano_rect
  (fun _ => Z -> list string) (* Signature of recursive calls *)
  (fun (z: Z) => nil:(list string)) (* Base case -- empty file *)
  (fun (prev: N) (rec: Z -> list string) (remaining: Z) =>
    recFileNameFrom rec file remaining disk)  (* Recursive case -- more file remaining *)
  (Z.to_N file.(fileSize))
  file.(fileSize).

Definition looksLikeRootkit (file: File) (disk: Disk) :=
  let parsed := parseFileNames file disk in
  exists (filename1 filename2: string),
    In filename1 parsed
    /\ In filename2 parsed
    /\ (FileNames.systemFile filename1)
    /\ (FileNames.systemFile filename2)
    /\ filename1 <> filename2.

Definition looksLikeRootkit_compute (file: File) (disk: Disk)
  (filename1 filename2: string) :=
     (existsb (string_eqb filename1) (parseFileNames file disk))
  && (existsb (string_eqb filename2) (parseFileNames file disk))
  && (FileNames.systemFile_compute filename1)
  && (FileNames.systemFile_compute filename2)
  && (negb (string_eqb filename1 filename2)).

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
    apply existsb_exists in H. destruct H. destruct H.
    apply string_eqb_reflection in H4. rewrite <- H4 in H. auto.
  split. 
    apply existsb_exists in H3. destruct H3. destruct H3.
    apply string_eqb_reflection in H4. rewrite <- H4 in H3. auto.
  split. apply systemFile_reflection. auto.
  split. apply systemFile_reflection. auto.

  compute. intros. apply <- string_eqb_reflection in H4.
  rewrite H4 in H0. discriminate H0.
Qed.
