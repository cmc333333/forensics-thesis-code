Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.

Require Import ByteData.
Require Import Fetch.
Require Import File.
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

Definition parseFirstFileNameAndFile (tar: File) 
  : @Fetch (ByteString*File) :=
  let firstHundredBytes := map tar.(data) (0 upto 100) in
  let fileName := fetch_flatten (takeWhile 
    (fun (byte: @Fetch Z) => match byte with
      | Found 0 => false (* stop *)
      | Found _ => true  (* continue *)
      | _ => false       (* stop *)
    end) firstHundredBytes) in
  (* File Size is encoded in octal, represented as ASCII characters. It begins
  at offset 124 and runs for 11 characters *)
  (seq_list tar.(data) 124 11) 
    _fflatmap_ (fun fileSizeList =>
  match (fromOctalAscii fileSizeList) _map_ (fun fileSize =>
    (fileName, 
      (mkFile None (* no id in child files*)
              fileSize
              (* Keep the deleted status of the tar *)
              tar.(deleted)  
              (* Header size = 512 *)
              (shift tar.(data) 512)
              (* Carry over fields from parent tar *)
              tar.(lastAccess)
              tar.(lastModification)
              tar.(lastCreated)
              tar.(lastDeleted)
    ))) with
    | error => ErrorString "Invalid Tar File Size"
    | value v => Found v
    end
  ).

Definition recFileNameFrom (nextCall: File -> list ByteString) 
  (remaining: File) : list ByteString :=
  if (remaining.(fileSize) <=? 0)
    then nil
  else match (parseFirstFileNameAndFile remaining) with
    | Found (fileName, file) =>
        (* Strip the first file out of the tar *)
        (* Round to the nearest 512 *)
        let firstFileSize := (
          if (file.(fileSize) mod 512 =? 0)
          then file.(fileSize) + 512
          else 512 * (2 + (file.(fileSize) / 512))) in
        let trimmedTar := 
          (mkFile None (* No id in child files *)
                  (remaining.(fileSize) - firstFileSize)
                  remaining.(deleted) (* Parent's value *)
                  (shift remaining.(data) firstFileSize)
                  (* Use parent's values *)
                  remaining.(lastAccess)
                  remaining.(lastModification)
                  remaining.(lastCreated)
                  remaining.(lastDeleted)
          ) in
        fileName :: (nextCall trimmedTar)
    | _ => nil
    end.

Definition parseFileNames (file: File): list (list Z) :=
  N.peano_rect
  (fun _ => File -> list (list Z)) (* Signature of recursive calls *)
  (fun (nilFile: File) => nil:(list (list Z))) (* Base case -- empty file *)
  (fun (prev: N) (rec: File -> list (list Z)) (remainingFile: File) =>
    recFileNameFrom rec remainingFile)  (* Recursive case -- more file remaining *)
  (Z.to_N file.(fileSize))
  file.

Definition looksLikeRootkit (file: File) :=
  exists (filename1 filename2: ByteString),
    (In filename1 (parseFileNames file))
    /\ (In filename2 (parseFileNames file))
    /\ (FileNames.systemFile filename1)
    /\ (FileNames.systemFile filename2)
    /\ filename1 <> filename2.
