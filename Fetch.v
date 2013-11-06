Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Export List.

Inductive Fetch {A:Type}: Type :=
  | Found: A -> Fetch
  | MissingAt: Z -> Fetch
  | ErrorString: string -> Fetch
.

(* Functional programming idioms *)
Definition fetch_flatmap {A B:Type} (opt: @Fetch A) (fn: A -> @Fetch B)
  : @Fetch B :=
  match opt with
    | Found a => fn a
    | MissingAt pos => MissingAt pos
    | ErrorString msg => ErrorString msg
  end.

Definition fetch_map {A B:Type} (opt: @Fetch A) (fn: A -> B)
  : @Fetch B :=
  match opt with
    | Found a => Found (fn a)
    | MissingAt pos => MissingAt pos
    | ErrorString msg => ErrorString msg
  end.

Infix "_fflatmap_" := fetch_flatmap (at level 50).
Infix "_fmap_" := fetch_map (at level 50).

Fixpoint fetch_flatten {A} (lst: list (@Fetch A)): list A :=
  match lst with
    | (Found head) :: tail => head :: (fetch_flatten tail)
    | _ :: tail => fetch_flatten tail
    | nil => nil
  end.
