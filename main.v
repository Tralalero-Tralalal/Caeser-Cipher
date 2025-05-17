From Coq Require Import Arith.
Require Import Lia.
Set Default Goal Selector "!".

Definition encrypt (n move_by : nat) : nat :=
    (n + move_by) mod 26.

Definition decrypt (c move_by : nat) : nat :=
  (c + (26 - move_by)) mod 26.

Inductive encrypted : nat -> nat -> Prop :=
  | encrypt_0 (n : nat) : 
      n < 26 -> encrypted n 0
  | encrypt_else (n : nat) (r : nat) :
      n < 26 -> r < 26 -> encrypted (encrypt n r) 0 -> encrypted n r.

Inductive decrypted : nat -> nat -> Prop :=
  | decrypt_0 (n : nat) : 
      n < 26 -> decrypted n 0
  | decrypt_else (n : nat) (r : nat) :
      n < 26 -> r < 26 -> decrypted (decrypt n r) 0 
      -> decrypted n r.

Example ex_encrypt : encrypted 20 9.
Proof.
  apply encrypt_else.
  - lia. - lia. - simpl. apply encrypt_0. unfold encrypt. simpl. lia. Qed.

Example ex_decrypt : decrypted 20 18.
Proof. apply decrypt_else. - lia. - lia. - simpl. apply decrypt_0. unfold decrypt.
simpl. lia. Qed.

Theorem decrypt_correctness :
  forall n m : nat, n < 26 -> m < 26 -> decrypted n m.
Proof.
  intros. apply decrypt_else. 
  - apply H.
  - apply H0.
  - apply decrypt_0. apply Nat.mod_upper_bound. lia.
Qed.

Theorem encrypt_correctness :
  forall n m : nat, n < 26 -> m < 26 -> encrypted n m.
Proof.
  intros. apply encrypt_else. 
  - apply H.
  - apply H0.
  - apply encrypt_0. apply Nat.mod_upper_bound. lia.
Qed.

Theorem decrypt_inverts_encrypt :
  forall n r,
    n < 26 -> r < 26 -> decrypted (encrypt n r) r.
Proof.
  intros. apply decrypt_else.
  - apply Nat.mod_upper_bound. lia.
  - apply H0.
  - apply decrypt_0. apply Nat.mod_upper_bound. lia.
Qed.

Theorem encrypt_inverts_decrypt :
  forall n r,
    n < 26 -> r < 26 -> encrypted (decrypt n r) r.
Proof.
  intros. apply encrypt_else.
  - apply Nat.mod_upper_bound. lia.
  - apply H0.
  - apply encrypt_0. apply Nat.mod_upper_bound. lia.
Qed.

