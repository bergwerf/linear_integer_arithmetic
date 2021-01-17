(* Formulae and interpretations of Presburger arithmetic. *)

Require Import Utf8 List.
From larith Require Import tactics notations utilities.
Import ListNotations.

(*
A note on variable indices: To greatly simplify certain proofs, we do not use
absolute variable indices. Instead the existential quantifier pushes a value on
the context stack, and a variable index refers to an index on the stack. It is
always possible to translate absolute indices to these relative indices.
*)
Section First_order_formulae.

Variable atom : Type.

(* Basic formula structure. *)
Inductive wff :=
  | WffAtom (a : atom)
  | WffAnd (φ ϕ : wff)
  | WffNot (φ : wff)
  | WffEx (φ : wff).

Variable domain : Type.
Variable Model : list domain -> atom -> Prop.

Fixpoint Realizes (Γ : list domain) (f : wff) :=
  match f with
  | WffAtom a  => Model Γ a
  | WffAnd φ ϕ => Realizes Γ φ /\ Realizes Γ ϕ
  | WffNot φ   => ¬Realizes Γ φ
  | WffEx φ    => ∃x, Realizes (x :: Γ) φ
  end.

End First_order_formulae.

Arguments WffAtom {_}.
Arguments WffAnd {_}.
Arguments WffNot {_}.
Arguments WffEx {_}.
Arguments Realizes {_ _}.

Notation model atom domain := (list domain -> atom -> Prop).
Notation "¬` φ" := (WffNot φ) (at level 30, right associativity, format "¬` φ").
Notation "φ ∧` ϕ" := (WffAnd φ ϕ) (right associativity, at level 35).
Notation "∃[ φ ]" := (WffEx φ) (format "∃[ φ ]").
Notation "A |= ( φ )[ Γ ]" := (Realizes A Γ φ)
  (at level 20, format "A  |=  ( φ )[ Γ ]").

Section Lemmas_about_realization.

Variable dom atomA atomB : Type.
Variable A : model atomA dom.
Variable B : model atomB dom.

Theorem realizes_ex φ ϕ :
  (∀Γ, A |= (φ)[Γ] <-> B |= (ϕ)[Γ]) ->
  ∀Γ, A |= (∃[φ])[Γ] <-> B |= (∃[ϕ])[Γ].
Proof.
intros eqv; simpl; split; intros [x Hx];
exists x; apply eqv, Hx.
Qed.

Theorem realizes_and φ1 φ2 ϕ1 ϕ2 :
  (∀Γ, A |= (φ1)[Γ] <-> B |= (ϕ1)[Γ]) ->
  (∀Γ, A |= (φ2)[Γ] <-> B |= (ϕ2)[Γ]) ->
  ∀Γ, A |= (φ1 ∧` φ2)[Γ] <-> B |= (ϕ1 ∧` ϕ2)[Γ].
Proof.
intros eqv1 eqv2; simpl; split; intros H.
all: split; [apply eqv1|apply eqv2]; apply H.
Qed.

End Lemmas_about_realization.

(* Atomic formulae for languages that we will be using. *)
Section Atomic_formulae_for_linear_integer_arithmetic.

Inductive std_term :=
  | Zero
  | One
  | Var (i : nat)
  | Add (x y : std_term).

Inductive std_atom :=
  | Std_eq (x y : std_term)
  | Std_le (x y : std_term).

Inductive r_atom :=
  | R_zero (i : nat)
  | R_one (i : nat)
  | R_add (i j k : nat)
  | R_eq (i j : nat)
  | R_le (i j : nat).

End Atomic_formulae_for_linear_integer_arithmetic.

Notation formula := (wff std_atom).
Notation rformula := (wff r_atom).

Definition formula_atom := @WffAtom std_atom.
Definition rformula_atom := @WffAtom r_atom.

Coercion formula_atom : std_atom >-> formula.
Coercion rformula_atom : r_atom >-> rformula.

(* Standard models of linear integer arithmetic. *)
Section Standard_models_of_linear_integer_arithmetic.

Fixpoint eval (Γ : list nat) (x : std_term) :=
  match x with
  | Zero    => 0
  | One     => 1
  | Var i   => nth i Γ 0
  | Add x y => eval Γ x + eval Γ y
  end.

Definition Nat (Γ : list nat) (a : std_atom) :=
  match a with
  | Std_eq x y => eval Γ x = eval Γ y
  | Std_le x y => eval Γ x ≤ eval Γ y
  end.

Definition NatR (Γ : list nat) (a : r_atom) :=
  let f := λ i, nth i Γ 0 in
  match a with
  | R_zero i    => f i = 0
  | R_one i     => f i = 1
  | R_add i j k => f i = f j + f k
  | R_eq i j    => f i = f j
  | R_le i j    => f i ≤ f j
  end.

End Standard_models_of_linear_integer_arithmetic.

(* Embedding formula in rformula. *)
Section Embedding_of_formula_in_rformula.

Fixpoint shift_vars n x :=
  match x with
  | Zero    => Zero
  | One     => One
  | Var i   => Var (n + i)
  | Add x y => Add (shift_vars n x) (shift_vars n y)
  end.

Notation "# i" := (Var i) (at level 9, format "# i").
Notation "x << n" := (shift_vars n x) (at level 10, format "x << n").

Theorem eval_shift_vars x Γ n :
  eval Γ (x<<n) = eval (skipn n Γ) x.
Proof.
induction x; simpl. 1,2: easy.
- revert Γ; induction n; simpl; intros.
  easy. destruct Γ; simpl. now destruct i. apply IHn.
- now rewrite IHx1, IHx2.
Qed.

Lemma reduce_std_term j x n :
  Σ ϕ, ∀Γ, Nat |= (Std_eq #j (x<<n))[Γ] <-> NatR |= (ϕ)[Γ].
Proof.
revert j n; induction x; intros.
- now exists (R_zero j).
- now exists (R_one j).
- now exists (R_eq j (n + i)).
- destruct (IHx1 0 (2 + n)) as [ϕ1 Hϕ1];
  destruct (IHx2 1 (2 + n)) as [ϕ2 Hϕ2].
  exists ∃[∃[R_add (2 + j) 0 1 ∧` ϕ1 ∧` ϕ2]].
  simpl in *; split.
  + intros H. exists (eval Γ (x2<<n)), (eval Γ (x1<<n)).
    repeat split. easy.
    * apply Hϕ1; simpl. now rewrite ?eval_shift_vars.
    * apply Hϕ2; simpl. now rewrite ?eval_shift_vars.
  + intros [n2 [n1 [H [H1 H2]]]].
    apply Hϕ1 in H1; rewrite eval_shift_vars in H1;
    apply Hϕ2 in H2; rewrite eval_shift_vars in H2; simpl in *.
    rewrite ?eval_shift_vars; congruence.
Qed.

Lemma reduce_std_eq x y Γ :
  Nat |= (Std_eq x y)[Γ] <-> 
  Nat |= (∃[Std_eq #0 (x<<1) ∧` Std_eq #0 (y<<1)])[Γ].
Proof.
split; simpl.
- intros H. exists (eval Γ x).
  split; now rewrite eval_shift_vars.
- intros [n [H1 H2]].
  rewrite eval_shift_vars in H1;
  rewrite eval_shift_vars in H2;
  simpl in *; congruence.
Qed.

Lemma reduce_std_le x y Γ :
  Nat |= (Std_le x y)[Γ] <-> 
  Nat |= (∃[∃[Std_le #0 #1 ∧` Std_eq #0 (x<<2) ∧` Std_eq #1 (y<<2)]])[Γ].
Proof.
split; simpl.
- intros H; exists (eval Γ y), (eval Γ x); repeat split.
  easy. all: now rewrite eval_shift_vars.
- intros [n2 [n1 [H [H1 H2]]]].
  rewrite eval_shift_vars in H1;
  rewrite eval_shift_vars in H2;
  simpl in *; congruence.
Qed.

Lemma std_le_iff_r_le i j Γ :
  Nat |= (Std_le #i #j)[Γ] <-> NatR |= (R_le i j)[Γ].
Proof.
easy.
Qed.

Theorem convert_std_atom_to_rformula (a : std_atom) :
  Σ ϕ, ∀Γ, NatR |= (ϕ)[Γ] <-> Nat |= (a)[Γ].
Proof.
destruct a.
- (* Equality relation. *)
  destruct reduce_std_term with (j:=0)(x:=x)(n:=1) as [ϕx Hx];
  destruct reduce_std_term with (j:=0)(x:=y)(n:=1) as [ϕy Hy].
  eexists; symmetry; etransitivity. apply reduce_std_eq.
  apply realizes_ex, realizes_and; easy.
- (* Less or equal relation. *)
  destruct reduce_std_term with (j:=0)(x:=x)(n:=2) as [ϕx Hx].
  destruct reduce_std_term with (j:=1)(x:=y)(n:=2) as [ϕy Hy].
  eexists; symmetry; etransitivity. apply reduce_std_le.
  apply realizes_ex, realizes_ex, realizes_and.
  apply std_le_iff_r_le. apply realizes_and; easy.
Qed.

Corollary convert_formula_to_rformula φ :
  Σ ϕ, ∀Γ, NatR |= (ϕ)[Γ] <-> Nat |= (φ)[Γ].
Proof.
induction φ.
- apply convert_std_atom_to_rformula.
- destruct IHφ1 as [ϕ1 H1], IHφ2 as [ϕ2 H2].
  exists (ϕ1 ∧` ϕ2); split.
  all: split; [apply H1|apply H2]; apply H.
- destruct IHφ as [ϕ H].
  exists (¬`ϕ); split; apply contra, H.
- destruct IHφ as [ϕ H].
  exists ∃[ϕ]; split;
  intros [x Hx]; exists x; apply H, Hx.
Qed.

End Embedding_of_formula_in_rformula.
