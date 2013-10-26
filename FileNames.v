Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Require Import ByteData.
Require Import Util.

Open Local Scope Z.

Definition trimFileNamePrefix (fileName: ByteString): ByteString :=
  let reversedName := rev fileName in
  rev (takeWhile (fun (char: Z) => (negb (orb (char =? 47)    (* '/' *)
                                              (char =? 92)))) (* '\' *)
                 reversedName).

Fixpoint ascii2Bytes (fileName: string): ByteString :=
  match fileName with
  | EmptyString => nil
  | String char tail => (Z.of_N (N_of_ascii char)) :: (ascii2Bytes tail)
  end.

Local Open Scope string_scope.

Definition systemFile (fileName: ByteString) :=
  In (trimFileNamePrefix fileName)
     (map ascii2Bytes ("ps" :: "netstat" :: "top" :: "ifconfig" 
                       :: "ssh" :: "rsync" :: "ProcMon.exe"
                       :: nil)).

Lemma systemFile_ex1 : 
  systemFile (ascii2Bytes "last/top").
Proof.
  compute. right. right. left. reflexivity.
Qed.

Lemma systemFile_ex2 : 
  ~(systemFile (ascii2Bytes "last/example.txt")).
Proof.
  compute. intro.
  repeat (destruct H; [ inversion H | ]).
  apply H.
Qed.
