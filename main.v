Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Require Import Nat.

Definition encrypt (n move_by : nat) : nat :=
  (n + move_by) mod 26.

Definition decrypt (c move_by : nat) : nat :=
  (c + (26 - (move_by mod 26))) mod 26.

Compute( encrypt (decrypt 30 1000) 1000 =? 30 mod 26).

Lemma encrypt_decrypt_inverse :
  forall n m : nat, encrypt (decrypt n m) m = n mod 26.
Proof.
  intros. unfold encrypt, decrypt. rewrite Nat.Div0.add_mod_idemp_l. 
  rewrite <- Nat.Div0.add_mod_idemp_r. rewrite <- Nat.add_assoc. Search (_ - ?n + ?n).
  rewrite Nat.sub_add. 
  - rewrite Nat.Div0.add_mod. rewrite Nat.Div0.mod_same.
  rewrite Nat.add_0_r. rewrite Nat.Div0.mod_mod. reflexivity.
  - Search(?a mod ?b <= ?b). apply Nat.Div0.mod_le.
Qed.
