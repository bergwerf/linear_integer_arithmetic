(* Models using binary numbers. *)

Require Vector.
Require Import Utf8 Bool Nat List Lia.
Require Import PeanoNat BinNat BinPos Nnat.
From larith Require Import tactics notations utilities.
From larith Require Import formulae automata automatic.
Import ListNotations.

(* A binary model for the relational language of linear integer arithmetic. *)
Definition BinR (Γ : list N) (a : r_atom) :=
  (let f := λ i, nth i Γ 0 in
  match a with
  | R_zero i    => f i = 0
  | R_one i     => f i = 1
  | R_add i j k => f i + f j = f k
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
    * erewrite ?nth_map. symmetry; apply Nat2N.inj_add.
      symmetry; apply H. all: easy.
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
Section Least_significant_bit_first_binary_numbers.

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

End Least_significant_bit_first_binary_numbers.

(* All r_atom formulas are regular. *)
Section Regular_relations.

Notation ctx := (vctx _ bnum).
Notation iffb := (Bool.eqb).
Notation "! b" := (negb b) (at level 20, format "! b").
Notation "l :0" := (map fst l) (left associativity, at level 40, format "l :0").
Notation "l :1" := (map snd l) (left associativity, at level 40, format "l :1").

Definition dfa_zero :=
  Automaton bool unit tt (λ _, true)
  (λ c _, if c then [] else [tt]).

Definition dfa_one :=
  Automaton bool bool false id
  (λ c s, if xorb c s then [true] else []).

Definition dfa_eq :=
  Automaton (bool × bool) unit tt (λ _, true)
  (λ c _, if iffb (fst c) (snd c) then [tt] else []).

Definition dfa_le :=
  Automaton (bool × bool) bool true id
  (λ c s, [let (l, r) := c in if s then !(l && !r) else !l && r]).

Definition dfa_add_trans xyz (c : bool) :=
  match xyz with
  | ((x, y), z) =>
    let sum := iffb (iffb x y) c in
    let carry := if c then x || y else x && y in
    if iffb sum z then [carry] else []
  end.

Definition dfa_add :=
  Automaton ((bool × bool) × bool) bool false negb dfa_add_trans.

Theorem dfa_zero_spec w :
  Language dfa_zero w <-> bnum w = 0%N.
Proof.
unfold Language; simpl.
induction w; simpl. easy.
destruct a, (bnum w); simpl; split; try easy.
1,2: intros H; now apply not_Accepts_nil in H.
apply IHw. intros H; apply IHw in H; easy.
Qed.

Lemma dfa_one_tail_spec w :
  Accepts dfa_one w [true] <-> Language dfa_zero w.
Proof.
unfold Language; induction w; simpl. easy. destruct a; simpl.
split; intros H; now apply not_Accepts_nil in H. apply IHw.
Qed.

Theorem dfa_one_spec w :
  Language dfa_one w <-> bnum w = 1%N.
Proof.
unfold Language; destruct w. easy. destruct b.
- rewrite bnum_cons_eq_one. simpl. rewrite dfa_one_tail_spec.
  apply dfa_zero_spec.
- split; simpl. intros H; now apply not_Accepts_nil in H.
  now destruct (bnum w).
Qed.

Theorem dfa_eq_spec w :
  Language dfa_eq w <-> bnum (w:0) = bnum (w:1).
Proof.
unfold Language; induction w. easy.
simpl in IHw; simpl Accepts; rewrite app_nil_r.
simpl map. rewrite bnum_cons_eq.
destruct a as [[] []]; simpl.
1,4: rewrite and_comm, and_remove_r; [apply IHw|easy].
all: apply exfalso_iff; [apply not_Accepts_nil|easy].
Qed.

Theorem dfa_le_Accepts w eq :
  Accepts dfa_le w [eq] <->
  (if eq then N.le else N.lt) (bnum (w:0)) (bnum (w:1)).
Proof.
revert eq; induction w; destruct eq.
1,2: easy. all: simpl Accepts; simpl map.
1: rewrite bnum_cons_le.
2: rewrite bnum_cons_lt.
all: destruct a as [[] []]; simpl.
all: try (rewrite and_remove_r; [|easy]).
all: try (rewrite or_remove_r; [|easy]).
1,3,4,7: rewrite <-N.lt_eq_cases.
all: apply IHw.
Qed.

Corollary dfa_le_spec w :
  Language dfa_le w <-> (bnum (w:0) <= bnum (w:1))%N.
Proof.
apply dfa_le_Accepts.
Qed.

Section Lemmas.

Lemma finite_type {letter} (A : automaton letter) n :
  (Σ Q, length Q = n /\ ∀s : state A, In s Q) -> Finite A n.
Proof.
intros [Q [Q_len Q_spec]]; exists Q; split. easy.
intros s; exists s; easy.
Qed.

Lemma finite_unit :
  Σ Q, length Q = 1 /\ ∀v : unit, In v Q.
Proof.
exists [tt]. split. easy.
intros []; apply in_eq.
Qed.

Lemma finite_bool :
  Σ Q, length Q = 2 /\ ∀b : bool, In b Q.
Proof.
exists [true; false]. split. easy.
intros []; simpl; auto.
Qed.

Lemma option_unit_dec (s t : option unit) :
  {s = t} + {s ≠ t}.
Proof.
destruct s as [[]|], t as [[]|].
1,4: now left. all: now right.
Qed.

Lemma option_bool_dec (s t : option bool) :
  {s = t} + {s ≠ t}.
Proof.
destruct s as [[]|], t as [[]|].
1,5,9: now left. all: now right.
Qed.

End Lemmas.

Theorem dfa_add_Accepts w c :
  Accepts dfa_add w [c] <->
  (bnum (w:0:0) + bnum (w:0:1) + bnum [c] = bnum (w:1))%N.
Proof.
revert c; induction w as [|[[x y] z] w]; intros. now destruct c.
simpl map; rewrite (bnum_cons x), (bnum_cons y), (bnum_cons z).
remember (bnum (w:0:0)) as xN;
remember (bnum (w:0:1)) as yN;
remember (bnum (w:1)) as zN.
assert(Accepts dfa_add w [] <-> False) by (split; [apply not_Accepts_nil|easy]).
destruct c, x, y, z; simpl Accepts; simpl bnum.
1,4,6,7,10,11,13,16: rewrite IHw; simpl bnum; lia.
all: rewrite H; lia.
Qed.

Corollary dfa_add_spec w :
  Language dfa_add w <-> (bnum (w:0:0) + bnum (w:0:1) = bnum (w:1))%N.
Proof.
unfold Language; rewrite dfa_add_Accepts.
simpl; now rewrite N.add_0_r.
Qed.

Lemma regular_R_zero i :
  regular (vec (S i)) (λ w, BinR (ctx w) (R_zero i)).
Proof.
eapply regular_ext. eapply regular_proj. eapply Regular.
- apply Automata.opt_det with (A:=dfa_zero); intros.
  simpl; destruct c; simpl; lia.
- apply Automata.opt_size, finite_type, finite_unit.
- apply option_unit_dec.
- apply Automata.opt_spec.
- intros; apply dfa_zero_spec.
- intros; simpl. erewrite <-(fin_spec i i) at 2.
  rewrite vctx_nth, transpose_nth; reflexivity. easy.
Qed.

Lemma regular_R_one i :
  regular (vec (S i)) (λ w, BinR (ctx w) (R_one i)).
Proof.
eapply regular_ext. eapply regular_proj. eapply Regular.
- apply Automata.opt_det with (A:=dfa_one); intros.
  simpl; destruct c, s; simpl; lia.
- apply Automata.opt_size, finite_type, finite_bool.
- apply option_bool_dec.
- apply Automata.opt_spec.
- intros; apply dfa_one_spec.
- intros; simpl. rewrite <-(fin_spec i i) at 2.
  rewrite vctx_nth, transpose_nth; reflexivity. easy.
Qed.

Lemma regular_R_eq i j :
  regular (vec (1 + max i j)) (λ w, BinR (ctx w) (R_eq i j)).
Proof.
remember (max i j) as n.
pose(f (c : vec (S n)) := (proj (fin n i) c, proj (fin n j) c)).
eapply regular_ext. eapply regular_proj with (f0:=f). eapply Regular.
- apply Automata.opt_det with (A:=dfa_eq); intros.
  simpl; destruct c as [[] []], s; simpl; lia.
- apply Automata.opt_size, finite_type, finite_unit.
- apply option_unit_dec.
- apply Automata.opt_spec.
- intros; apply dfa_eq_spec.
- intros; simpl.
  rewrite <-(fin_spec n i), <-(fin_spec n j).
  rewrite ?vctx_nth, ?transpose_nth, ?map_map; reflexivity. all: lia.
Qed.

Lemma regular_R_le i j :
  regular (vec (1 + max i j)) (λ w, BinR (ctx w) (R_le i j)).
Proof.
remember (max i j) as n.
pose(f (c : vec (S n)) := (proj (fin n i) c, proj (fin n j) c)).
eapply regular_proj with (f0:=f).
eapply Regular with (r_automaton:=dfa_le).
- easy.
- apply finite_type, finite_bool.
- apply bool_dec.
- apply dfa_le_spec.
- intros; simpl.
  rewrite <-(fin_spec n i), <-(fin_spec n j).
  rewrite ?vctx_nth, ?transpose_nth, ?map_map; reflexivity. all: lia.
Qed.

Lemma regular_R_add i j k :
  regular (vec (1 + max (max i j) k)) (λ w, BinR (ctx w) (R_add i j k)).
Proof.
remember (max (max i j) k) as n.
pose(f (c : vec (S n)) :=
  ((proj (fin n i) c, proj (fin n j) c), proj (fin n k) c)).
eapply regular_ext. eapply regular_proj with (f0:=f). eapply Regular.
- apply Automata.opt_det with (A:=dfa_add); intros.
  simpl; destruct c as [[[] []] []], s; simpl; lia.
- apply Automata.opt_size, finite_type, finite_bool.
- apply option_bool_dec.
- apply Automata.opt_spec.
- intros; apply dfa_add_spec.
- intros; simpl.
  rewrite <-(fin_spec n i), <-(fin_spec n j), <-(fin_spec n k).
  rewrite ?vctx_nth, ?transpose_nth, ?map_map; reflexivity. all: lia.
Qed.

Corollary regular_r_atom a :
  Σ n, regular (vec n) (λ w, BinR (ctx w) a).
Proof.
destruct a.
- exists (S i); apply regular_R_zero.
- exists (S i); apply regular_R_one.
- exists (1 + max (max i j) k); apply regular_R_add.
- exists (1 + max i j); apply regular_R_eq.
- exists (1 + max i j); apply regular_R_le.
Qed.

End Regular_relations.
