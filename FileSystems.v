Require Import Coq.ZArith.ZArith.

Require Import ByteData.

Inductive FileSystem: Type :=
  | Ext2FS: Z -> FileSystem
  | TarFS: FileSystem -> Z -> FileSystem
  | MockFS: ByteData -> FileSystem
.

Fixpoint eqb (lhs rhs: FileSystem) :=
  match (lhs, rhs) with
  | ((Ext2FS l), (Ext2FS r)) => Z.eqb l r
  | ((TarFS lfs l), (TarFS rfs r)) => (andb (eqb lfs rfs) (Z.eqb l r))
  | _ => false
  end.

Lemma eqb_reflection (lhs rhs: FileSystem) :
  eqb lhs rhs = true -> lhs = rhs.
Proof.
  generalize rhs.
  induction lhs. 
    (* Ext2FS *)
    destruct rhs0; 
      [| simpl; intros; inversion H | simpl; intros; inversion H].
    unfold eqb. intros. apply Z.eqb_eq in H. rewrite H. reflexivity.
    (* TarFS *)
    destruct rhs0; 
      [simpl; intros; inversion H | | simpl; intros; inversion H].
      intros. unfold eqb in H. 
      apply Bool.andb_true_iff in H. destruct H.
      apply Z.eqb_eq in H0. rewrite H0.
      apply IHlhs in H. rewrite H.
      reflexivity.
    (* MockFS *)
    destruct rhs0; 
      [simpl; intros; inversion H | simpl; intros; inversion H | 
       simpl; intros; inversion H].
Qed.
