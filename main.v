From Coq Require Import Arith.
From Coq Require Import Bool.
From Coq Require Export Strings.String.
From Coq Require Import FunctionalExtensionality.
From Coq Require Import List.
Require Import Lia.
Import ListNotations.
Set Default Goal Selector "!".

Definition total_map (A : Type) := nat -> A.

Definition t_empty {A : Type} (v : A) : total_map A :=
  (fun _ => v).

Definition t_update {A : Type} (m : total_map A)
                    (x : nat) (v : A) :=
  fun x' => if Nat.eqb x x' then v else m x'.

Notation "'_' '!->' v" := (t_empty v)
  (at level 100, right associativity).
Example example_empty := (_ !-> false).

Notation "x '!->' v ';' m" := (t_update m x v)
                              (at level 100, v at next level, right associativity).

Inductive letters :=
  | LA | LB | LC | LD | LE | LF | LG | LH | LI | LJ | LK | LL | LM | LN
  | LO | LP | LQ | LR | LS | LT | LU | LV | LW | LX | LY | LZ.

Definition example_letter_map :=
  ( 0 !-> LA;
    1 !-> LB;
    2 !-> LC;
    3 !-> LD;
    4 !-> LE;
    5 !-> LF;
    6 !-> LG;
    7 !-> LH;
    8 !-> LI;
    9 !-> LJ;
    10 !-> LK;
    11 !-> LL;
    12 !-> LM;
    13 !-> LN;
    14 !-> LO;
    15 !-> LP;
    16 !-> LQ;
    17 !-> LR;
    18 !-> LS;
    19 !-> LT;
    20 !-> LU;
    21 !-> LV;
    22 !-> LW;
    23 !-> LX;
    24 !-> LY;
    25 !-> LZ;
    _ !-> LA  (* Default value *)
  ).

Fixpoint letter_eqb (l1 l2 : letters) : bool :=
  match l1, l2 with
  | LA, LA | LB, LB | LC, LC | LD, LD | LE, LE | LF, LF | LG, LG
  | LH, LH | LI, LI | LJ, LJ | LK, LK | LL, LL | LM, LM | LN, LN
  | LO, LO | LP, LP | LQ, LQ | LR, LR | LS, LS | LT, LT | LU, LU
  | LV, LV | LW, LW | LX, LX | LY, LY | LZ, LZ => true
  | _, _ => false
  end.

Definition cipher (n add_by : nat) : option letters :=
  if n <? 26 then
    let idx := (n + add_by) mod 26 in
    Some (example_letter_map idx)
  else
    None.

Compute(cipher 25 2).

Lemma cipher_returns_some :
  forall n add_by,
    0 < n < 26 ->
    exists l, cipher n add_by = Some l.
Proof.
Admitted.

