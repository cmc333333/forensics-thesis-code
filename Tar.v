Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.

Require Import ByteData.
Require Import Fetch.
Require Import File.
Require Import FileData.
Require Import FileNames.
Require Import Util.

Local Open Scope Z.

Definition ByteString := list Z.

Fixpoint fromOctalAscii (bytes: list Z) : Exc Z :=
  match bytes with
  | nil => value 0
  | byte :: tail => match (fromOctalAscii tail) with
    | error => error
    | value rest => if (andb (48 <=? byte) (byte <=? 56))
      then value (rest + ((byte-48) 
                          * (8 ^ (Z.of_nat (length tail)))))
      else error (* Invalid character *)
    end
  end.

Definition parseFirstFileNameAndSize (tar: File) (offset: Z) (disk: Disk)
  : @Fetch (ByteString*Z) :=
  let firstHundredBytes := map (fetchByte tar disk) 
                               (offset upto (100 + offset)) in
  let fileName := fetch_flatten (takeWhile 
    (fun (byte: @Fetch Z) => match byte with
      | Found 0 => false (* stop *)
      | Found _ => true  (* continue *)
      | _ => false       (* stop *)
    end) firstHundredBytes) in
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

Definition recFileNameFrom (nextCall: Z -> list ByteString) 
  (tar: File) (remaining: Z) (disk: Disk) : list ByteString :=
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

Definition parseFileNames (file: File) (disk: Disk): list (list Z) :=
  N.peano_rect
  (fun _ => Z -> list (list Z)) (* Signature of recursive calls *)
  (fun (z: Z) => nil:(list (list Z))) (* Base case -- empty file *)
  (fun (prev: N) (rec: Z -> list (list Z)) (remaining: Z) =>
    recFileNameFrom rec file remaining disk)  (* Recursive case -- more file remaining *)
  (Z.to_N file.(fileSize))
  file.(fileSize).

Definition looksLikeRootkit (file: File) (disk: Disk) :=
  exists (filename1 filename2: ByteString),
    (existsb (listZ_eqb filename1) (parseFileNames file disk)) = true
    /\ (existsb (listZ_eqb filename2) (parseFileNames file disk)) = true
    /\ (FileNames.systemFile filename1)
    /\ (FileNames.systemFile filename2)
    /\ (listZ_eqb filename1 filename2) = false.
