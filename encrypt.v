Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Import Nat Div0.

Definition encrypt (n move_by : nat) : nat :=
  (n + move_by) mod 26.

Definition decrypt (c move_by : nat) : nat :=
  (c + (26 - (move_by mod 26))) mod 26.

Compute( encrypt (decrypt 30 1000) 1000 =? 30 mod 26).

Lemma encrypt_decrypt_inverse :
  forall n m : nat, encrypt (decrypt n m) m = n mod 26.
Proof.
  intros n k.
  unfold encrypt, decrypt.
  rewrite add_mod_idemp_l. rewrite <- add_mod_idemp_r.
  rewrite <- add_assoc. rewrite sub_add.
  - rewrite <- add_mod_idemp_r. rewrite mod_same.
    rewrite add_0_r. reflexivity.
  -
    apply lt_le_incl. apply mod_bound_pos. 
    apply le_0_l. lia.
Qed.

Lemma decrypt_encrypt_inverse :
  forall n m : nat, decrypt (encrypt n m) m = n mod 26.
Proof.
  intros n k.
  unfold encrypt, decrypt.
  rewrite add_mod_idemp_l. rewrite add_shuffle0. 
  rewrite <- add_mod_idemp_r. rewrite <- add_assoc.
  rewrite sub_add.
  - rewrite <- add_mod_idemp_r. rewrite mod_same.
    rewrite add_0_r. reflexivity.  
  - apply lt_le_incl. apply mod_bound_pos. apply le_0_l. lia.
Qed.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.

Separate Extraction encrypt decrypt.
