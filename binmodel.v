(* An automatic structure for rformula. *)

Require Vector.
Require Import Utf8 Bool List Lia.
Require Import PeanoNat BinNat Nnat.
From larith Require Import tactics notations utilities vector binary.
From larith Require Import formulae automata regular automatic.
Import ListNotations.

(* A model for the relational language on a domain of binary strings. *)
Definition BinR (a : rel_atom) (Γ : list N) :=
  (let f := λ i, nth i Γ 0 in
  match a with
  | rel_zero i    => f i = 0
  | rel_one i     => f i = 1
  | rel_add i j k => f i + f j = f k
  | rel_eq i j    => f i = f j
  | rel_le i j    => f i <= f j
  end)%N.

Lemma nth_app_default {X} i l (d : X) :
  nth i (l ++ [d]) d = nth i l d.
Proof.
revert l; induction i; destruct l; simpl in *; try easy.
destruct i; reflexivity.
Qed.

Theorem BinR_default a Γ :
  BinR a Γ <-> BinR a (Γ ++ [0%N]).
Proof.
destruct a; simpl;
rewrite ?nth_app_default; easy.
Qed.

Theorem NatR_BinR_isomorphism φ Γ :
  NatR |= (φ)[Γ] <-> BinR |= (φ)[map N.of_nat Γ].
Proof.
apply isomorphic_model; clear Γ.
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

Section Regularity_of_BinR.

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

Lemma finite_unit :
  Σ Q, length Q = 1 /\ ∀v : unit, In v Q.
Proof.
exists [tt]. split. easy.
intros []; apply in_eq.
Defined.

Lemma finite_bool :
  Σ Q, length Q = 2 /\ ∀b : bool, In b Q.
Proof.
exists [true; false]. split. easy.
intros []; simpl; auto.
Defined.

Lemma option_unit_dec (s t : option unit) :
  {s = t} + {s ≠ t}.
Proof.
destruct s as [[]|], t as [[]|].
1,4: now left. all: now right.
Defined.

Lemma option_bool_dec (s t : option bool) :
  {s = t} + {s ≠ t}.
Proof.
destruct s as [[]|], t as [[]|].
1,5,9: now left. all: now right.
Defined.

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

Lemma regular_rel_zero i :
  regular (λ w : list (vec (S i)),
    BinR (rel_zero i) (ctx w)).
Proof.
eapply regular_ext. eapply regular_proj. eapply Regular.
- apply Automata.opt_det with (A:=dfa_zero); intros.
  simpl; destruct c; simpl; auto.
- apply Automata.opt_size, finite_unit.
- apply option_unit_dec.
- apply Automata.opt_spec.
- intros; apply dfa_zero_spec.
- intros; simpl. erewrite <-(fin_spec i i) at 2.
  rewrite vctx_nth; reflexivity. easy.
Defined.

Lemma regular_rel_one i :
  regular (λ w : list (vec (S i)),
    BinR (rel_one i) (ctx w)).
Proof.
eapply regular_ext. eapply regular_proj. eapply Regular.
- apply Automata.opt_det with (A:=dfa_one); intros.
  simpl; destruct c, s; simpl; auto.
- apply Automata.opt_size, finite_bool.
- apply option_bool_dec.
- apply Automata.opt_spec.
- intros; apply dfa_one_spec.
- intros; simpl. rewrite <-(fin_spec i i) at 2.
  rewrite vctx_nth; reflexivity. easy.
Defined.

Lemma regular_rel_eq i j :
  regular (λ w : list (vec (1 + max i j)),
    BinR (rel_eq i j) (ctx w)).
Proof.
remember (max i j) as n.
pose(f (c : vec (S n)) := (vnth c (fin n i), vnth c (fin n j))).
eapply regular_ext. eapply regular_proj with (pr:=f). eapply Regular.
- apply Automata.opt_det with (A:=dfa_eq); intros.
  simpl; destruct c as [[] []], s; simpl; auto.
- apply Automata.opt_size, finite_unit.
- apply option_unit_dec.
- apply Automata.opt_spec.
- intros; apply dfa_eq_spec.
- intros; simpl.
  rewrite <-(fin_spec n i), <-(fin_spec n j).
  rewrite ?vctx_nth, ?map_map; reflexivity. all: lia.
Defined.

Lemma regular_rel_le i j :
  regular (λ w : list (vec (1 + max i j)),
    BinR (rel_le i j) (ctx w)).
Proof.
remember (max i j) as n.
pose(f (c : vec (S n)) := (vnth c (fin n i), vnth c (fin n j))).
eapply regular_proj with (pr:=f).
eapply Regular with (r_dfa:=dfa_le).
- easy.
- apply finite_bool.
- apply bool_dec.
- apply dfa_le_spec.
- intros; simpl.
  rewrite <-(fin_spec n i), <-(fin_spec n j).
  rewrite ?vctx_nth, ?map_map; reflexivity. all: lia.
Defined.

Lemma regular_rel_add i j k :
  regular (λ w : list (vec (1 + max (max i j) k)),
    BinR (rel_add i j k) (ctx w)).
Proof.
remember (max (max i j) k) as n.
pose(f (c : vec (S n)) :=
  ((vnth c (fin n i), vnth c (fin n j)), vnth c (fin n k))).
eapply regular_ext. eapply regular_proj with (pr:=f). eapply Regular.
- apply Automata.opt_det with (A:=dfa_add); intros.
  simpl; destruct c as [[[] []] []], s; simpl; auto.
- apply Automata.opt_size, finite_bool.
- apply option_bool_dec.
- apply Automata.opt_spec.
- intros; apply dfa_add_spec.
- intros; simpl.
  rewrite <-(fin_spec n i), <-(fin_spec n j), <-(fin_spec n k).
  rewrite ?vctx_nth, ?map_map; reflexivity. all: lia.
Defined.

Lemma nth_firstn {X} i n l (d : X) :
  i < n -> nth i (firstn n l) d = nth i l d.
Proof.
revert i n; induction l; destruct n, i; simpl; try easy.
intros H; apply IHl, Lt.lt_S_n, H.
Qed.

Theorem Automatic_rel_atom (a : rel_atom) :
  Automatic BinR bnum (wff_atom a).
Proof.
destruct a;
[ exists (1 + i)
| exists (1 + i)
| exists (1 + max (max i j) k)
| exists (1 + max i j)
| exists (1 + max i j)].
all: split.
2: apply regular_rel_zero.
3: apply regular_rel_one.
4: apply regular_rel_add.
5: apply regular_rel_eq.
6: apply regular_rel_le.
all: rewrite Nat.add_comm; intros Γ; simpl.
all: rewrite ?nth_firstn; try easy.
all: lia.
Defined.

End Regularity_of_BinR.

Theorem BinR_dec φ :
  {∃Γ, BinR |= (φ)[Γ]} + {∀Γ, BinR |= (¬`φ)[Γ]}.
Proof.
apply automatic_structure_dec with (default:=0%N)(decode:=bnum)(encode:=bits).
apply BinR_default.
apply bnum_bits_id.
apply bnum_padding.
apply Automatic_rel_atom.
Defined.

(* The Grande Final Theorem! *)
Theorem Nat_dec φ :
  {∃Γ, Nat |= (φ)[Γ]} + {∀Γ, Nat |= (¬`φ)[Γ]}.
Proof.
destruct convert_formula_to_rformula with (φ:=φ) as [ϕ ϕ_spec].
destruct BinR_dec with (φ:=ϕ).
- left; destruct e as [Γ HΓ].
  exists (map N.to_nat Γ). apply ϕ_spec, NatR_BinR_isomorphism.
  erewrite map_map, map_ext. rewrite map_id; apply HΓ. apply N2Nat.id.
- right; intros Γ HΓ.
  apply ϕ_spec, NatR_BinR_isomorphism, r in HΓ; easy.
Defined.

Section Evaluation.

Notation "φ ∨` ϕ" := (¬`(¬`φ ∧` ¬`ϕ)) (at level 35).
Notation "φ ⟹ ϕ" := (¬`(φ ∧` ¬`ϕ)) (at level 40).
Notation "∀[ φ ]" := (¬`∃[¬`φ]) (format "∀[ φ ]").
Notation "i =` j" := (wff_atom (rel_eq i j)) (at level 25).
Notation "i ≤` j" := (wff_atom (rel_le i j)) (at level 25).
Notation "i ≠` j" := (¬`(i =` j)) (at level 25).
Notation "i <` j" := (i ≤` j ∧` i ≠` j) (at level 25).
Notation Zero i   := (wff_atom (rel_zero i)).
Notation One i    := (wff_atom (rel_one i)).
Notation decide φ := (if BinR_dec φ then true else false).

(*
Evaluation
----------
It is possible to evaluate the decision procedure, but it is extremely slow! The
decision itself takes place in Set and can be evaluated, but I do not know how
to retrieve the actual witness in Prop.

Here are some examples of trivial valid formulae in the relational language that
can be decided within a few seconds.
```
Compute decide ∃[One 0].
Compute decide ∀[0 ≤` 0].
Compute decide ∃[0 ≠` 0].
Compute decide ∀[Zero 0].
Compute decide (0 <` 1).
Compute decide (0 <` 1 ∧` 1 <` 0).
Compute decide (0 ≤` 1 ∧` 1 ≤` 0 ∧` 0 ≠` 1).
```

Slightly non-trivial examples (in particular quantifiers over more complex
formulas) become unfeasible. I did not have the patience to let the following
examples finish.
```
Compute decide ∀[0 <` 1 ∨` 1 <` 0].
Compute decide ∀[∀[0 ≤` 1 ∧` 1 ≤` 0 ⟹ 0 =` 1]].
```

The terrible performance is of course entirely to blame on this implementation.
There exist efficient implementations of this decision procedure which could
easily evaluate the above examples.

There are some opportunities to improve the performance without altering the
construction in a fundamental way:
+ The automaton construction could be separated from the specification.
+ The path search could use a search depth and visited nodes list.

It would also be interesting to (effectively) produce witnesses in Set. Note
that the path search could directly use the automaton accept function, and that
it could just use lists to represent paths (all properties can be deferred to
its specification). Introducing binary trees probably doesn't make sense,
because at that point there are other much more limiting factors.
*)

Example decide_a_formula_by_computation :
  decide ∃[0 ≠` 0] = false.
Proof.
vm_compute; reflexivity.
Qed.

End Evaluation.
