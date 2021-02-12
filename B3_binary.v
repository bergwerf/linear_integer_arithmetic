(* Least-significant bit encoding and decoding of numbers. *)

Require Import Bool BinNat BinPos Nnat.
From larith Require Import A_setup B1_utils.

Open Scope N.

Fixpoint pbits (p : positive) : list bool :=
  match p with
  | xI q => true :: pbits q
  | xO q => false :: pbits q
  | xH   => [true]
  end.

Definition bits (n : N) :=
  match n with
  | 0%N     => []
  | N.pos p => pbits p
  end. 

Fixpoint bnum (bits : list bool) : N :=
  match bits with
  | []      => 0
  | b :: bs =>
    match (bnum bs) with
    | 0       => if b then 1 else 0
    | N.pos p => N.pos (if b then p~1 else p~0)
    end
  end.

Theorem bnum_bits_id n :
  bnum (bits n) = n.
Proof.
destruct n; simpl. easy.
induction p; simpl.
1,2: rewrite IHp. all: easy.
Qed.

Theorem bnum_padding b :
  bnum (b ++ [false]) = bnum b.
Proof.
induction b; simpl.
easy. now rewrite IHb.
Qed.

Theorem bnum_cons x xs :
  bnum (x :: xs) = bnum [x] + 2 * (bnum xs).
Proof.
simpl; now destruct x, (bnum xs).
Qed.

Corollary bnum_cons_eq_one xs :
  bnum (true :: xs) = 1 <-> bnum xs = 0.
Proof.
rewrite bnum_cons; simpl bnum.
destruct (bnum xs); easy.
Qed.

Theorem bnum_cons_compare x xs y ys :
  bnum (x :: xs) ?= bnum (y :: ys) =
  Pos.switch_Eq (Bool.compare x y) (bnum xs ?= bnum ys).
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
now destruct x, y, (bnum xs ?= bnum ys).
Qed.

Corollary bnum_cons_le x xs y ys :
  bnum (x :: xs) <= bnum (y :: ys) <->
  bnum xs < bnum ys \/ (bnum xs = bnum ys /\ Bool.le x y).
Proof.
rewrite <-?N.compare_le_iff, <-N.compare_lt_iff;
rewrite <-N.compare_eq_iff, bnum_cons_compare.
destruct x, y, (bnum xs ?= bnum ys) eqn:H; simpl.
all: try (rewrite and_remove_r; [|easy]).
all: try (rewrite or_remove_r; [|easy]).
all: try (rewrite or_comm, or_remove_r; [|easy]).
all: try easy.
Qed.

Corollary bnum_cons_lt x xs y ys :
  bnum (x :: xs) < bnum (y :: ys) <->
  bnum xs < bnum ys \/ (bnum xs = bnum ys /\ Bool.lt x y).
Proof.
rewrite <-?N.compare_lt_iff, <-N.compare_eq_iff, bnum_cons_compare.
destruct x, y, (bnum xs ?= bnum ys) eqn:H; simpl.
all: try (rewrite and_remove_r; [|easy]).
all: try (rewrite or_remove_r; [|easy]).
all: try (rewrite or_comm, or_remove_r; [|easy]).
all: try easy.
Qed.

Close Scope N.
