Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Export List.

Open Local Scope Z.

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

Lemma wrap_with_found {X:Type} : forall (x y:X), Found x = Found y -> x = y.
  Proof.
  intros. injection H. auto.
Qed.

Definition eqb {T:Type} (lhs rhs: @Fetch T) (t_eqb: T->T->bool) :=
  match (lhs, rhs) with
  | (Found l, Found r) => t_eqb l r
  | (MissingAt l, MissingAt r) => l =? r
  | (_, _) => false
  end.

Definition Z_feqb (lhs rhs: @Fetch Z) := eqb lhs rhs Z.eqb.

Lemma Z_feqb_reflection (lhs rhs: @Fetch Z):
  Z_feqb lhs rhs = true -> lhs = rhs.
Proof.
  intros. unfold Z_feqb in H. unfold eqb in H.
  destruct lhs.
    destruct rhs; [| discriminate H | discriminate H]. 
      apply Z.eqb_eq in H. rewrite H. reflexivity.
    destruct rhs; [discriminate H | | discriminate H].
      apply Z.eqb_eq in H. rewrite H. reflexivity.
    discriminate H.
Qed.
