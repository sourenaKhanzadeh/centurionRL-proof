(* Basics.v - First Coq Proof *)

Require Import Nat.

Theorem add_comm : forall x y : nat, x + y = y + x.
Proof.
  intros.
  apply Nat.add_comm.
Qed.
