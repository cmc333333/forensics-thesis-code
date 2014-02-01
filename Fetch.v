Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Export List.

Local Open Scope N.

Inductive Fetch {A:Type}: Type :=
  | Found: A -> Fetch
  | MissingAt: N -> Fetch
  | ErrorString: string -> Fetch
.

(* Functional programming idioms *)
Definition fetch_flatmap {A B:Type} (opt: @Fetch A) 
  (fn: A -> @Fetch B)
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

Definition N_feqb (lhs rhs: @Fetch N) := eqb lhs rhs N.eqb.

Lemma N_feqb_reflection (lhs rhs: @Fetch N):
  N_feqb lhs rhs = true -> lhs = rhs.
Proof.
  intros. unfold N_feqb in H. unfold eqb in H.
  destruct lhs.
    destruct rhs; [| discriminate H | discriminate H]. 
      apply N.eqb_eq in H. rewrite H. reflexivity.
    destruct rhs; [discriminate H | | discriminate H].
      apply N.eqb_eq in H. rewrite H. reflexivity.
    discriminate H.
Qed.

Lemma found_fmap_found : 
  forall (A B: Type) (fetchA: @Fetch A) (fn: A -> B) (bval: B),
    (fetchA _fmap_ fn) = Found bval ->
      exists (aval: A), fetchA = Found aval /\ fn aval = bval.
Proof.
  intros.
  destruct fetchA; [ | discriminate H | discriminate H].
  exists a. injection H.
  intros. auto.
Qed.

Lemma found_fflatmap_found : 
  forall (A B: Type) (fetchA: @Fetch A) (fn: A -> @Fetch B) (bval: B),
    (fetchA _fflatmap_ fn) = Found bval ->
      exists (aval: A), fetchA = Found aval /\ fn aval = Found bval.
Proof.
  intros.
  destruct fetchA; [ | discriminate H | discriminate H].
  exists a. auto.
Qed.

Lemma found_fflatmap_found_twice :
  forall (A B: Type) (fetch1 fetch2: @Fetch A) (fn1 fn2: A -> @Fetch B)
         (b: B),
    (forall (a: A), fetch1 = Found a -> fetch2 = Found a) ->
      (forall (a: A) (b: B), fn1 a = Found b -> fn2 a = Found b) ->
        fetch1 _fflatmap_ fn1 = Found b ->
          fetch2 _fflatmap_ fn2 = Found b.
Proof.
  intros.
  apply found_fflatmap_found in H1.
  destruct H1 as [aval [avalH fn1H]].
  apply H in avalH. rewrite avalH.
  apply H0 in fn1H.
  simpl. assumption.
Qed.
