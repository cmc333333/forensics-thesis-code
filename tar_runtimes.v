Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Require Import Byte.
Require Import ByteData.
Require Import Fetch.
Require Import File.
Require Import FileData.
Require Import Tar.

Local Open Scope N.
Local Open Scope char.

Fixpoint create (level:nat) : Map_N_Byte :=
  match level with
  | O => MN.empty Byte
  | S level_minus_one =>
      let initial := (N.of_nat level_minus_one) * 512 in
      (MN.add (0 + initial) "a"    (MN.add (1 + initial) "b"
      (MN.add (2 + initial) "c"    (MN.add (3 + initial) "d"
      (MN.add (4 + initial) "e"    (MN.add (5 + initial) "f"
      (MN.add (6 + initial) "g"    (MN.add (7 + initial) "h"
      (MN.add (8 + initial) "i"    (MN.add (9 + initial) "j"
      (MN.add (10 + initial) "000" (MN.add (124 + initial) "0"
      (MN.add (125 + initial) "0"  (MN.add (126 + initial) "0"
      (MN.add (127 + initial) "0"  (MN.add (128 + initial) "0"
      (MN.add (129 + initial) "0"  (MN.add (130 + initial) "0"
      (MN.add (131 + initial) "0"  (MN.add (132 + initial) "0"
      (MN.add (133 + initial) "0"  (MN.add (134 + initial) "0"
      (create level_minus_one)))))))))))))))))))))))
  end.

Definition f_of (level:nat) := 
    mkFile (FileIds.MockId (Disk_of_Map_N_Byte (create level)))
           (512 * (N.of_nat level)) false None None None None.

Definition disk (n:N): @Fetch Byte := MissingAt n.

Open Scope nat.
Open Scope string.
Definition f1: File := f_of 1.
Compute (last (parseFileNames f1 disk) "tst").
Definition f5: File := f_of 5.
Compute (last (parseFileNames f5 disk) "tst").
Definition f10: File := f_of 10.
Compute (last (parseFileNames f10 disk) "tst").
Definition f50: File := f_of 50.
Compute (last (parseFileNames f50 disk) "tst").
Definition f100: File := f_of 100.
Compute (last (parseFileNames f100 disk) "tst").
Definition f500: File := f_of 500.
Compute (last (parseFileNames f500 disk) "tst").
Definition f1000: File := f_of 1000.
Compute (last (parseFileNames f1000 disk) "tst").
Definition f5000: File := f_of 5000.
Compute (last (parseFileNames f5000 disk) "tst").
