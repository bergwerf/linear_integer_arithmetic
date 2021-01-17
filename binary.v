(* Models using binary numbers. *)

Require Import Utf8 PeanoNat BinNat Nnat List.
From larith Require Import tactics notations utilities formulae.
Import Nat ListNotations.

(* A binary model for the relational language of linear integer arithmetic. *)
Definition BinR (Γ : list N) (a : r_atom) :=
  (let f := λ i, nth i Γ 0 in
  match a with
  | R_zero i    => f i = 0
  | R_one i     => f i = 1
  | R_add i j k => f i = f j + f k
  | R_eq i j    => f i = f j
  | R_le i j    => f i <= f j
  end)%N.

Theorem NatR_iff_BinR φ Γ :
  NatR |= (φ)[Γ] <-> BinR |= (φ)[map N.of_nat Γ].
Proof.
apply similar_models; clear Γ.
- intros y; exists (N.to_nat y). apply N2Nat.id.
- intros; destruct a; simpl.
  all: replace (0%N) with (N.of_nat 0) by easy.
  + split. apply nth_map1. apply nth_map2, Nat2N.inj.
  + replace 1%N with (N.of_nat 1) by easy.
    split. apply nth_map1. apply nth_map2, Nat2N.inj.
  + split; intros.
    * erewrite ?nth_map1. apply Nat2N.inj_add.
      1,2: reflexivity. easy.
    * erewrite ?nth_map1 in H.
      rewrite <-Nat2N.inj_add in H; apply Nat2N.inj in H.
      apply H. all: easy.
  + erewrite ?nth_map1. 2,3: reflexivity.
    split. congruence. apply Nat2N.inj.
  + erewrite ?nth_map1. 2,3: reflexivity.
    split; intros.
    * apply compare_le_iff in H.
      now rewrite Nat2N.inj_compare in H.
    * apply compare_le_iff.
      now rewrite Nat2N.inj_compare.
Qed.
