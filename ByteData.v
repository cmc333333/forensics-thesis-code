Require Import Coq.ZArith.ZArith.
Require Import FSets.FMaps.
Require Import FSets.FMapAVL.

Require Import Fetch.

Open Local Scope Z.

(* instantiation of the AVL module that implements the finite map interface *)
Module MZ := FSets.FMapAVL.Make Z_as_OT.

(* the type of finite maps from Z to Z *)
Definition Map_Z_Z : Type := MZ.t Z.

(* lookup in a finite map *)
Definition find k (m: Map_Z_Z) := MZ.find k m.

(* create a new finite map by adding/overwriting an element with an existing
   finite map *)
Definition update (p: Z*Z) (m: Map_Z_Z) := MZ.add (fst p) (snd p) m.

(* notation for building finite maps *)
(* k |-> v   says that key k maps to value v *)
Notation "k |-> v" := (pair k v) (at level 60).
Notation "[ ]" := (MZ.empty Z).
Notation "[ p1 , .. , pn ]" := (update p1 .. (update pn []) .. ).

Definition ByteString := list Z.
Definition ByteData := Z -> (@Fetch Z).
Definition Disk := ByteData.

Bind Scope ByteData_scope with Disk.

Definition Disk_of_Map_Z_Z (map: Map_Z_Z) : Disk :=
  fun (key: Z) => match (find key map) with
  | error => MissingAt key
  | value v => Found v
  end.

Coercion Disk_of_Map_Z_Z : Map_Z_Z >-> Disk.

(* Change the "zero" index; i.e. "shift" the bytes *)
Definition shift (bytes: ByteData) (shiftAmount index: Z) 
  : Fetch :=
  bytes (shiftAmount + index).
