Require Import Coq.ZArith.ZArith.
Require Import FSets.FMaps.
Require Import FSets.FMapAVL.

Require Import Byte.
Require Import Fetch.

Open Local Scope N.

(* instantiation of the AVL module that implements the finite map interface *)
Module MN := FSets.FMapAVL.Make N_as_OT.

(* the type of finite maps from Z to Z *)
Definition Map_N_Byte : Type := MN.t Byte.

(* lookup in a finite map *)
Definition find k (m: Map_N_Byte) := MN.find k m.

(* create a new finite map by adding/overwriting an element with an existing
   finite map *)
Definition update (p: N*Byte) (m: Map_N_Byte) := MN.add (fst p) (snd p) m.

(* notation for building finite maps *)
(* k |-> v   says that key k maps to value v *)
Notation "k |-> v" := (pair k v) (at level 60).
Notation "[ ]" := (MN.empty Byte).
Notation "[ p1 , .. , pn ]" := (update p1 .. (update pn []) .. ).

Definition ByteData := N -> (@Fetch Byte).
Definition Disk := ByteData.

Bind Scope ByteData_scope with Disk.

Definition Disk_of_Map_N_Byte (map: Map_N_Byte) : Disk :=
  fun (key: N) => match (find key map) with
  | error => MissingAt key
  | value v => Found v
  end.

Coercion Disk_of_Map_N_Byte : Map_N_Byte >-> Disk.

(* Change the "zero" index; i.e. "shift" the bytes *)
Definition shift (bytes: ByteData) (shiftAmount index: N) 
  : Fetch :=
  bytes (shiftAmount + index).
