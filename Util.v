Require Import Coq.PArith.BinPos.
Require Import Coq.ZArith.ZArith.
Require Export List.

Require Import ByteData.
Require Import Fetch.

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
