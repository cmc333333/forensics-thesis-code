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

Definition systemFile_compute (fileName: ByteString) :=
  existsb (listZ_eqb (trimFileNamePrefix fileName))
          (map ascii2Bytes ("ps" :: "netstat" :: "top" :: "ifconfig" 
                            :: "ssh" :: "rsync" :: "ProcMon.exe"
                            :: nil)).

Lemma systemFile_reflection (fileName: ByteString) :
  systemFile_compute fileName = true -> systemFile fileName.
Proof.
  intros. unfold systemFile_compute in H. unfold systemFile.
  apply existsb_exists in H. destruct H. destruct H.
  apply listZ_eqb_reflection in H0. rewrite H0. auto.
Qed.
          

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
