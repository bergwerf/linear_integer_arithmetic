(* Models using binary numbers. *)

Require Vector.
Require Import Utf8 PeanoNat BinNat Nnat List.
From larith Require Import tactics notations utilities.
From larith Require Import formulae automata automatic.
Import ListNotations.

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
  + split. apply nth_map. apply nth_map_inj, Nat2N.inj.
  + replace 1%N with (N.of_nat 1) by easy.
    split. apply nth_map. apply nth_map_inj, Nat2N.inj.
  + split; intros.
    * erewrite ?nth_map. apply Nat2N.inj_add.
      1,2: reflexivity. easy.
    * erewrite ?nth_map in H.
      rewrite <-Nat2N.inj_add in H; apply Nat2N.inj in H.
      apply H. all: easy.
  + erewrite ?nth_map. 2,3: reflexivity.
    split. congruence. apply Nat2N.inj.
  + erewrite ?nth_map. 2,3: reflexivity.
    split; intros.
    * apply Nat.compare_le_iff in H.
      now rewrite Nat2N.inj_compare in H.
    * apply Nat.compare_le_iff.
      now rewrite Nat2N.inj_compare.
Qed.

(* Translate lists of booleans to a binary number. *)
Section Least_significant_bit_first_binary_coding.

Fixpoint binnum (l : list bool) :=
  match l with
  | []      => 0%N
  | b :: l' =>
    match (binnum l') with
    | 0%N     => if b then 1%N else 0%N
    | N.pos p => N.pos (if b then xI p else xO p)
    end
  end.

End Least_significant_bit_first_binary_coding.

(* All r_atom formulas are regular. *)
Section Regular_relations.

Notation ctx := (vctx _ binnum).

Theorem regular_binnum_zero :
  regular bool (λ w, binnum w = N0).
Proof.
pose(A := Automaton bool unit tt (λ _, true) (λ c _, if c then [] else [tt])).
eapply Regular with (r_automaton:=A).
- exists [tt]; simpl; split. reflexivity.
  intros s; exists s; destruct s; split. now left. easy.
- left; now destruct s, t.
- unfold Language; simpl.
  intros w; induction w; simpl.
  easy. destruct a, (binnum w); simpl; split; try easy.
  1,2: intros H; now apply not_Accepts_nil in H.
  apply IHw. intros H; apply IHw in H; easy.
Qed.

Corollary regular_R_zero i :
  regular (vec (S i)) (λ w, BinR (ctx w) (R_zero i)).
Proof.
(* Somehow, generalize the result from regular_binnum_zero. *)
Abort.

End Regular_relations.
