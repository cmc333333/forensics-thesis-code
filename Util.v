Require Import Coq.PArith.BinPos.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Export List.

Require Import ByteData.
Require Import Fetch.

Open Local Scope bool.
Open Local Scope Z.

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

Definition opt_eqbZ (lhs rhs: Exc Z): bool :=
  match (lhs, rhs) with
  | (Some l, Some r) => l =? r
  | (None, None) => true
  | _ => false
  end.

Infix "_flatmap_" := flatmap (at level 50).
Infix "_map_" := opt_map (at level 50).

Definition range (start: Z) (exclusiveEnd: Z) : list Z :=
  N.peano_rect
  (fun _ => Z -> list Z) (* Signature of recursive calls *)
  (fun (start: Z) => nil) (* Base case *)
  (fun (counter: N) (rec: Z -> list Z) (start: Z) =>
    if (exclusiveEnd <=? start)
    then nil
    else start :: (rec (start + 1)))
  (Z.to_N (exclusiveEnd - start))
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
Definition seq_list (disk: Disk) (start length: Z): @Fetch (list Z) :=
  match length with
    | Z0 => Found nil
    | Zpos l => 
      (Pos.peano_rec
        (fun _ => Z -> @Fetch (list Z))
        (fun (start': Z) => (disk start') _fmap_ (fun nextEl => nextEl :: nil))
        (fun _ (seq_list_aux_pred_l: Z -> @Fetch (list Z)) (start': Z) => 
          (disk start') _fflatmap_ (fun nextEl =>
            (seq_list_aux_pred_l (Z.succ start')) _fmap_ (fun tail =>
              nextEl :: tail
            )
          )
        )
      )
      l
      start
    | Zneg _ => MissingAt length (* Should never be reached *)
  end.

(* little endian unsigned *)
Fixpoint lendu (l : list Z) : Z := 
match l with 
  | nil => 0
  | a :: l' => (a + (256 * lendu l'))
end.   

Definition seq_lendu (disk: Disk) (offset: Z) (length: Z): @Fetch Z :=
  (seq_list disk offset length) _fmap_ (fun tail => lendu tail).

Fixpoint listZ_eqb (l r: list Z) := match (l, r) with
  | (nil, nil) => true
  | (l :: ltail, r :: rtail) => (andb (l =? r) (listZ_eqb ltail rtail))
  | (_, _) => false
end.

Lemma listZ_reflection (l r: list Z) :
  listZ_eqb l r = true -> l = r.
Proof.
  admit.
Qed.

Definition optZ_eqb (lhs rhs: Exc Z) := match (lhs, rhs) with
  | (None, None) => true
  | (Some l, Some r) => l =? r
  | _ => false
end.

Lemma optZ_eqb_reflection (lhs rhs: Exc Z) :
  optZ_eqb lhs rhs = true -> lhs = rhs.
Proof.
  intros. unfold optZ_eqb in H.
  destruct lhs. 
    destruct rhs; [|discriminate H]. apply Z.eqb_eq in H. rewrite H. reflexivity.
    destruct rhs; [discriminate H|]. auto.
Qed.
 
Definition ascii_eqb (lhs rhs: ascii) : bool :=
  match (lhs, rhs) with
  | (Ascii l1 l2 l3 l4 l5 l6 l7 l8, Ascii r1 r2 r3 r4 r5 r6 r7 r8) =>
      (Bool.eqb l1 r1) && (Bool.eqb l2 r2)
      && (Bool.eqb l3 r3) && (Bool.eqb l4 r4)
      && (Bool.eqb l5 r5) && (Bool.eqb l6 r6)
      && (Bool.eqb l7 r7) && (Bool.eqb l8 r8)
  end.

Fixpoint string_eqb (lhs rhs: string) :=
  match (lhs, rhs) with
  | (EmptyString, EmptyString) => true
  | (String l ltail, String r rtail) =>
      (ascii_eqb l r) && (string_eqb ltail rtail)
  | _ => false
  end.
