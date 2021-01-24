(* LSB list bool encoding and decoding of binary numbers. *)

Require Import Utf8 Bool List Lia.
Require Import BinNat BinPos Nnat.
From larith Require Import tactics notations utilities.
Import ListNotations.

Fixpoint bnum (bits : list bool) :=
  match bits with
  | []      => 0%N
  | b :: bs =>
    match (bnum bs) with
    | 0%N     => if b then 1%N else 0%N
    | N.pos p => N.pos (if b then p~1 else p~0)
    end
  end.

Theorem bnum_cons x xs :
  (bnum (x :: xs) = bnum [x] + 2 * (bnum xs))%N.
Proof.
simpl; now destruct x, (bnum xs).
Qed.

Corollary bnum_cons_eq_one l :
  bnum (true :: l) = 1%N <-> bnum l = 0%N.
Proof.
rewrite bnum_cons; simpl bnum. lia.
Qed.

Theorem bnum_cons_compare x xs y ys :
  (bnum (x :: xs) ?= bnum (y :: ys) =
  Pos.switch_Eq (Bool.compare x y) (bnum xs ?= bnum ys))%N.
Proof.
simpl; destruct x, y, (bnum xs), (bnum ys); simpl; try easy.
1: rewrite Pos.compare_xI_xI. 4: rewrite Pos.compare_xO_xO.
3: apply Pos.compare_xO_xI. 2: apply Pos.compare_xI_xO.
all: now destruct (p ?= p0)%positive.
Qed.

Corollary bnum_cons_eq x xs y ys :
  bnum (x :: xs) = bnum (y :: ys) <-> x = y /\ bnum xs = bnum ys.
Proof.
rewrite <-?N.compare_eq_iff, bnum_cons_compare.
now destruct x, y, (bnum xs ?= bnum ys)%N.
Qed.

Corollary bnum_cons_le x xs y ys :
  (bnum (x :: xs) <= bnum (y :: ys) <->
  bnum xs < bnum ys \/ bnum xs = bnum ys /\ Bool.le x y)%N.
Proof.
rewrite <-?N.compare_le_iff, <-N.compare_lt_iff;
rewrite <-N.compare_eq_iff, bnum_cons_compare.
destruct x, y, (bnum xs ?= bnum ys)%N eqn:H; simpl.
all: try (rewrite and_remove_r; [|easy]).
all: try (rewrite or_remove_r; [|easy]).
all: try (rewrite or_comm, or_remove_r; [|easy]).
all: try easy.
Qed.

Corollary bnum_cons_lt x xs y ys :
  (bnum (x :: xs) < bnum (y :: ys) <->
  bnum xs < bnum ys \/ bnum xs = bnum ys /\ Bool.lt x y)%N.
Proof.
rewrite <-?N.compare_lt_iff, <-N.compare_eq_iff, bnum_cons_compare.
destruct x, y, (bnum xs ?= bnum ys)%N eqn:H; simpl.
all: try (rewrite and_remove_r; [|easy]).
all: try (rewrite or_remove_r; [|easy]).
all: try (rewrite or_comm, or_remove_r; [|easy]).
all: try easy.
Qed.
