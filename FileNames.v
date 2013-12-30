Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Require Import ByteData.
Require Import StringOps.
Require Import Util.

Open Local Scope Z.
Open Local Scope char.
Open Local Scope string.


Definition trimFileNamePrefix (fileName: string): string :=
  let reversedName := rev fileName in
  list2string
    (rev (takeWhile (fun (char: ascii) => 
                        (negb (orb (ascii_eqb char "/")
                                   (ascii_eqb char "\"))))
                   reversedName)).

Definition systemFile (fileName: string) :=
  In (trimFileNamePrefix fileName)
     ("ps" :: "netstat" :: "top" :: "ifconfig" :: "ssh" 
           :: "rsync" :: "ProcMon.exe" :: nil).

Definition systemFile_compute (fileName: string) :=
  existsb (string_eqb (trimFileNamePrefix fileName))
          ("ps" :: "netstat" :: "top" :: "ifconfig" :: "ssh"
                :: "rsync" :: "ProcMon.exe" :: nil).

Lemma systemFile_reflection (fileName: string) :
  systemFile_compute fileName = true -> systemFile fileName.
Proof.
  intros. unfold systemFile_compute in H. unfold systemFile.
  apply existsb_exists in H. destruct H. destruct H.
  apply string_eqb_reflection in H0. rewrite H0. auto.
Qed.
          

Lemma systemFile_ex1 : 
  systemFile "last/top".
Proof.
  compute. right. right. left. reflexivity.
Qed.

Lemma systemFile_ex2 : 
  ~(systemFile "last/example.txt").
Proof.
  compute. intro.
  repeat (destruct H; [ inversion H | ]).
  apply H.
Qed.
