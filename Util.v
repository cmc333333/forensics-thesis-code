Require Import Coq.PArith.BinPos.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Export List.

Require Import Byte.
Require Import ByteData.
Require Import DiskSubset.
Require Import Fetch.

Local Open Scope bool.
Local Open Scope N.

(* Functional programming idioms *)
Definition flatmap {A B: Type} (opt: Exc A) (fn: A -> Exc B) 
  : Exc B :=
  match opt with
    | Some v => fn v
    | None => None
  end.

Definition opt_map {A B: Type} (opt: Exc A) (fn: A -> B) 
  : Exc B :=
  match opt with
    | Some v => value (fn v)
    | None => None
  end.

Definition opt_eqbN (lhs rhs: Exc N): bool :=
  match (lhs, rhs) with
  | (Some l, Some r) => l =? r
  | (None, None) => true
  | _ => false
  end.

Infix "_flatmap_" := flatmap (at level 50).
Infix "_map_" := opt_map (at level 50).

Definition range (start: N) (exclusiveEnd: N) : list N :=
  N.peano_rect
  (fun _ => N -> list N) (* Signature of recursive calls *)
  (fun (start: N) => nil) (* Base case *)
  (fun (counter: N) (rec: N -> list N) (start: N) =>
    if (exclusiveEnd <=? start)
    then nil
    else start :: (rec (start + 1)))
  (exclusiveEnd - start)
  start.

Infix "upto" := range (at level 50).

Fixpoint takeWhile {A} (predicate: A->bool) (lst: list A) 
  : list A :=
  match lst with
  | head :: tail => if (predicate head) 
                    then (head 
                          :: (takeWhile predicate tail))
                    else nil
  | nil => nil
end.

Fixpoint flatten {A} (lst: list (Exc A)): list A :=
  match lst with
    | (value head) :: tail => head :: (flatten tail)
    | error :: tail => flatten tail
    | nil => nil
  end.


(* from a Disk, extract the list of elements
  [ disk start; disk (start + 1); ... ; disk (start + length - 1) ] *)
Definition seq_list (disk: Disk) (start length: N): @Fetch (list Byte) :=
  match length with
    | 0 => Found nil
    | N.pos l => 
      (Pos.peano_rec
        (fun _ => N -> @Fetch (list Byte))
        (fun (start': N) => (disk start') _fmap_ (fun nextEl => nextEl :: nil))
        (fun _ (seq_list_aux_pred_l: N -> @Fetch (list Byte)) (start': N) => 
          (disk start') _fflatmap_ (fun nextEl =>
            (seq_list_aux_pred_l (N.succ start')) _fmap_ (fun tail =>
              nextEl :: tail
            )
          )
        )
      )
      l
      start
  end.

Lemma seq_list_subset :
  forall (sub super: Disk) (start length: N) (val: list Byte),
    sub ⊆ super ->
      seq_list sub start length = Found val ->
        seq_list super start length = Found val.
Proof.
  intros sub super start length val subsetH.
  generalize start. clear start.
  generalize val. clear val.
  unfold disk_subset in subsetH.
  destruct length.
    unfold seq_list. auto.
    apply Pos.peano_ind with (p := p).
    simpl. 
    intros val start.
    remember (sub start).
    destruct f; [| intros contra; discriminate contra
                 | intros contra; discriminate contra].
      symmetry in Heqf. apply subsetH in Heqf.
      rewrite Heqf. auto.
    intros p0. intros H.
    unfold seq_list. 
    rewrite Pos.peano_rect_succ. rewrite Pos.peano_rect_succ.
    intros val st0. generalize val. clear val.
    remember (sub st0).
    destruct f.
      symmetry in Heqf. apply subsetH in Heqf.
      rewrite Heqf. simpl. 
      unfold seq_list in H.
      unfold fetch_map at 4.
      intros val Hsub.
      apply H.
      simpl in H0.
      unfold seq_list in H.
    rewrite H with (val := val).
    symmetry in Heqf.
    unfold seq_list in H.
    rewrite H with (val := val).
    unfold fetch_flatmap in H0.
    rewrite H0 in H.
    destruct (sub start).
      intros H2. 
      symmetry in Heqf.
    simpl.
    intros val.
    remember (sub start).
    destruct f; [| intros contra; discriminate contra
                 | intros contra; discriminate contra].
      symmetry in Heqf. apply subsetH in Heqf.
      rewrite Heqf. simpl.
    intros. 
  induction length.
    unfold seq_list. auto.
    apply Pos.peano_ind with (p := p).
    simpl. 
    remember (sub start).
    destruct f; [| intros contra; discriminate contra
                 | intros contra; discriminate contra].
      symmetry in Heqf. apply subsetH in Heqf.
      rewrite Heqf. auto.
    intros p0.
    intros H.
    unfold seq_list. rewrite Pos.peano_rect_succ. rewrite Pos.peano_rect_succ.
    remember (sub start).
    destruct f; [| intros contra; discriminate contra
                 | intros contra; discriminate contra].
      symmetry in Heqf. apply subsetH in Heqf.
      rewrite Heqf. simpl.
    intros. 
    cbv delta.
    compute.
  (fun (_ : positive) (seq_list_aux_pred_l : N -> Fetch) (start' : N) =>
   super start'
   _fflatmap_ (fun nextEl : Byte =>
               seq_list_aux_pred_l (N.succ start')
               _fmap_ (fun tail : list Byte => nextEl :: tail)))).
    apply subsetH.
    destruct f.
    unfold fetch_flatmap.
    intros.
    unfold seq_list.
    rewrite Pos.peano_rect_succ.
    unfold seq_list in H0.
      rewrite Pos.peano_rect_succ in H0.
      intros contra. discriminate contra.
      apply <- subsetH in Heqf.
      apply <- Heqf in subsetH.
    destruct (sub start).
      assert
    intr
      apply subset H.
    unfold seq_list.
  induction length using Pos.peano_rec.
    unfold seq_list. auto.
    apply Pos.peano_case.


(* little endian unsigned *)
Fixpoint lendu (l : list Byte) : N := 
match l with 
  | nil => 0
  | a :: l' => (N_of_ascii a) + (256 * lendu l')
end.   

Definition seq_lendu (disk: Disk) (offset: N) (length: N): @Fetch N :=
  (seq_list disk offset length) _fmap_ (fun tail => lendu tail).

Lemma seq_lendu_subset :
  forall (sub super: Disk) (offset length value: N),
    seq_lendu 

Fixpoint listN_Byte_eqb (l r: list (N*Byte)) := match (l, r) with
  | (nil, nil) => true
  | ((lN, lByte) :: ltail, (rN, rByte) :: rtail) =>
      (lN =? rN)
      && Byte.eqb lByte rByte
      && listN_Byte_eqb ltail rtail
  | (_, _) => false
end.

Lemma listN_Byte_eqb_reflection (l r: list (N*Byte)) :
  listN_Byte_eqb l r = true <-> l = r.
Proof.
  split. (* -> *)
    generalize r.
    induction l.
      destruct r0. 
        reflexivity.
        vm_compute. intros. inversion x.
    intros.
    destruct a.
    destruct r0.
      inversion H.

      destruct p.
      unfold listN_Byte_eqb in H.
      apply Bool.andb_true_iff in H. destruct H.
      apply Bool.andb_true_iff in H. destruct H.

      apply N.eqb_eq in H. rewrite H.
      apply Byte.eqb_reflection in H1. rewrite H1.
      apply IHl in H0. rewrite H0.
      reflexivity.
  (* <- *)
    generalize r.
    induction l.
      destruct r0. 
        reflexivity.
        intros. inversion H.
    intros.
    destruct r0.
      inversion H.
      
      destruct a. destruct p.
      unfold listN_Byte_eqb. apply Bool.andb_true_iff.
      inversion H.
      split. apply Bool.andb_true_iff. split.
        apply N.eqb_eq. reflexivity.
        apply Byte.eqb_reflection. reflexivity.
        rewrite <- H3 at 1. apply IHl in H3. auto.
Qed.
      

Fixpoint listN_eqb (l r: list N) := match (l, r) with
  | (nil, nil) => true
  | (l :: ltail, r :: rtail) =>
      (l =? r) 
      && listN_eqb ltail rtail
  | (_, _) => false
end.

Lemma listN_eqb_reflection (l r: list N) :
  listN_eqb l r = true <-> l = r.
Proof.
  split. (* -> *)
    generalize r.
    induction l.
      destruct r0. 
        reflexivity.
        vm_compute. intros. inversion x.
    intros.
    destruct r0.
      inversion H.

      unfold listN_eqb in H.
      apply Bool.andb_true_iff in H. destruct H.
      apply N.eqb_eq in H. rewrite H.
      apply IHl in H0. rewrite H0.
      reflexivity.
  (* <- *)
    generalize r.
    induction l.
      destruct r0. 
        reflexivity.
        intros. inversion H.
    intros.
    destruct r0.
      inversion H.
      
      unfold listN_eqb. apply Bool.andb_true_iff.
      inversion H.
      split.
        apply N.eqb_eq. reflexivity.
        rewrite <- H2 at 1. apply IHl in H2. auto.
Qed.

Definition optN_eqb (lhs rhs: Exc N) := match (lhs, rhs) with
  | (None, None) => true
  | (Some l, Some r) => l =? r
  | _ => false
end.

Lemma optN_eqb_reflection (lhs rhs: Exc N) :
  optN_eqb lhs rhs = true -> lhs = rhs.
Proof.
  intros. unfold optN_eqb in H.
  destruct lhs. 
    destruct rhs; [|discriminate H]. apply N.eqb_eq in H. rewrite H. reflexivity.
    destruct rhs; [discriminate H|]. auto.
Qed.
