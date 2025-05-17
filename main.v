From Coq Require Import Arith.
From Coq Require Import Bool.
From Coq Require Export Strings.String.
From Coq Require Import FunctionalExtensionality.
From Coq Require Import List.
Require Import Lia.
Import ListNotations.
Set Default Goal Selector "!".

Definition encrypt (n move_by : nat) : nat :=
    (n + move_by) mod 26.

Definition decrypt (c move_by : nat) : nat :=
  (c + (26 - move_by)) mod 26.

Inductive encrypted : nat -> nat -> Prop :=
  | encrypt_rotation_0 (n : nat) : n < 26 -> encrypted n 0
  | rotation_step (n : nat) (r : nat) :
      n < 26 -> r < 26 -> encrypted ((n - 1) mod 26) (S r).

Inductive decrypted : nat -> nat -> Prop :=
  | decrypt_rotation_0 (n : nat) : decrypted n 0
  | decrypt_rotation_step (n : nat) (r : nat) :
      decrypted n r -> decrypted ((n + 1) mod 26) (S r).

Lemma equiv_encrypt_decrypt :
  forall n move_by : nat,
    n < 26 -> move_by < 26 ->
    encrypt (decrypt n move_by) move_by = n /\
    decrypt (encrypt n move_by) move_by = n.
Proof.
  intros n move_by Hn Hm.
  unfold encrypt, decrypt.
  split. Admitted.

Lemma encryption_ex : encrypted 5 10.
Proof.
  apply rotation_step with (n := 6) (r := 9).
  - lia. - lia.
Qed.

