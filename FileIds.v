Require Import Coq.ZArith.ZArith.

Require Import ByteData.

Inductive FileId: Type :=
  | Ext2Id: N -> FileId
  | TarId: FileId -> N -> FileId
  | MockId: ByteData -> FileId
.

Fixpoint eqb (lhs rhs: FileId) :=
  match (lhs, rhs) with
  | ((Ext2Id l), (Ext2Id r)) => N.eqb l r
  | ((TarId lfs l), (TarId rfs r)) => (andb (eqb lfs rfs) (N.eqb l r))
  | _ => false
  end.

Lemma eqb_reflection (lhs rhs: FileId) :
  eqb lhs rhs = true -> lhs = rhs.
Proof.
  generalize rhs.
  induction lhs. 
    (* Ext2Id *)
    destruct rhs0; 
      [| simpl; intros; inversion H | simpl; intros; inversion H].
    unfold eqb. intros. apply N.eqb_eq in H. rewrite H. reflexivity.
    (* TarId *)
    destruct rhs0; 
      [simpl; intros; inversion H | | simpl; intros; inversion H].
      intros. unfold eqb in H. 
      apply Bool.andb_true_iff in H. destruct H.
      apply N.eqb_eq in H0. rewrite H0.
      apply IHlhs in H. rewrite H.
      reflexivity.
    (* MockId *)
    destruct rhs0; 
      [simpl; intros; inversion H | simpl; intros; inversion H | 
       simpl; intros; inversion H].
Qed.
