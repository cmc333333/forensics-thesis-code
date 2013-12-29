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
  intros.
  induction lhs. 
    (* Ext2FS *)
    destruct rhs; 
      [ | contradict H; simpl; auto | contradict H; simpl; auto].
    unfold eqb in H. apply Z.eqb_eq in H. rewrite H. reflexivity.
    (* TarFS *)
    destruct rhs; 
      [ contradict H; simpl; auto | | contradict H; simpl; auto].
    admit.
    (* MockFS *)
    destruct rhs; 
      [ contradict H; simpl; auto | contradict H; simpl; auto | ].
    unfold eqb in H. contradict H. auto.
Qed.
