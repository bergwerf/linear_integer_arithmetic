(* Formulae and interpretations of Presburger arithmetic. *)

Require Import Utf8 Nat List.
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
  | wff_atom (a : atom)
  | wff_not (φ : wff)
  | wff_and (φ ϕ : wff)
  | wff_ex (φ : wff).

Variable domain : Type.
Variable Model : atom -> list domain -> Prop.

Fixpoint Realizes (f : wff) (Γ : list domain) :=
  match f with
  | wff_atom a  => Model a Γ
  | wff_not φ   => ¬Realizes φ Γ
  | wff_and φ ϕ => Realizes φ Γ /\ Realizes ϕ Γ
  | wff_ex φ    => ∃x, Realizes φ (x :: Γ)
  end.

Definition Use φ n := ∀Γ, Realizes φ Γ <-> Realizes φ (firstn n Γ).

Section Facts_about_usage.

Theorem Use_not φ n :
  Use φ n -> Use (wff_not φ) n.
Proof.
split; simpl; apply contra, H.
Qed.

Theorem Use_and φ ϕ n :
  Use φ n -> Use ϕ n -> Use (wff_and φ ϕ) n.
Proof.
intros Hφ Hϕ; split; simpl.
all: split; [apply (Hφ Γ)|apply (Hϕ Γ)]; apply H.
Qed.

Theorem Use_ex φ n :
  Use φ (S n) -> Use (wff_ex φ) n.
Proof.
split; simpl; intros [x Hx];
exists x; now apply (H (x :: Γ)).
Qed.

Theorem Use_weaken φ m n :
  Use φ m -> m <= n -> Use φ n.
Proof.
intros use le; intros Γ.
rewrite (use (firstn n Γ)).
now rewrite firstn_firstn, min_l.
Qed.

End Facts_about_usage.

End First_order_formulae.

Arguments wff_atom {_}.
Arguments wff_not {_}.
Arguments wff_and {_}.
Arguments wff_ex {_}.
Arguments Realizes {_ _}.
Arguments Use {_ _}.

Notation model atom domain := (atom -> list domain -> Prop).
Notation "¬` φ" := (wff_not φ)(right associativity, at level 30, format "¬` φ").
Notation "φ ∧` ϕ" := (wff_and φ ϕ) (right associativity, at level 35).
Notation "∃[ φ ]" := (wff_ex φ) (format "∃[ φ ]").
Notation "A |= ( φ )[ Γ ]" := (Realizes A φ Γ)
  (at level 20, format "A  |=  ( φ )[ Γ ]").

Section Results_about_realization.

Section Reductions.

Variable dom atomA atomB : Type.
Variable A : model atomA dom.
Variable B : model atomB dom.

Theorem Realizes_ex φ ϕ :
  (∀Γ, A |= (φ)[Γ] <-> B |= (ϕ)[Γ]) ->
  ∀Γ, A |= (∃[φ])[Γ] <-> B |= (∃[ϕ])[Γ].
Proof.
intros eqv; simpl; split; intros [x Hx];
exists x; apply eqv, Hx.
Qed.

Theorem Realizes_and φ1 φ2 ϕ1 ϕ2 :
  (∀Γ, A |= (φ1)[Γ] <-> B |= (ϕ1)[Γ]) ->
  (∀Γ, A |= (φ2)[Γ] <-> B |= (ϕ2)[Γ]) ->
  ∀Γ, A |= (φ1 ∧` φ2)[Γ] <-> B |= (ϕ1 ∧` ϕ2)[Γ].
Proof.
intros eqv1 eqv2; simpl; split; intros H.
all: split; [apply eqv1|apply eqv2]; apply H.
Qed.

End Reductions.

Section Isomorphism.

Variable domA domB atom : Type.
Variable A : model atom domA.
Variable B : model atom domB.
Variable f : domA -> domB.
Hypothesis f_surj : ∀y, ∃x, f x = y.

Theorem isomorphic_model :
  (∀a Γ, A a Γ <-> B a (map f Γ)) ->
  ∀φ Γ, A |= (φ)[Γ] <-> B |= (φ)[map f Γ].
Proof.
intros eqv; induction φ; simpl; intros.
- apply eqv.
- split; apply contra, IHφ.
- split; intros H.
  all: split; [apply IHφ1|apply IHφ2]; apply H.
- split.
  + intros [x Hx]; exists (f x).
    rewrite <-map_cons; apply IHφ, Hx.
  + intros [y Hy]. destruct (f_surj y) as [x R]; subst.
    exists x; apply IHφ, Hy.
Qed.

End Isomorphism.

End Results_about_realization.

(* Atomic formulae for languages that we will be using. *)
Section Atomic_formulae_for_linear_arithmetic.

Inductive la_term :=
  | la_zero
  | la_one
  | la_var (i : nat)
  | la_add (x y : la_term).

Inductive la_atom :=
  | la_eq (x y : la_term)
  | la_le (x y : la_term).

Inductive rel_atom :=
  | rel_zero (i : nat)
  | rel_one (i : nat)
  | rel_add (i j k : nat)
  | rel_eq (i j : nat)
  | rel_le (i j : nat).

End Atomic_formulae_for_linear_arithmetic.

Notation formula := (wff la_atom).
Notation rformula := (wff rel_atom).

Definition formula_atom := @wff_atom la_atom.
Definition rformula_atom := @wff_atom rel_atom.

Coercion formula_atom : la_atom >-> formula.
Coercion rformula_atom : rel_atom >-> rformula.

(* Standard models of linear arithmetic. *)
Section Standard_models_of_linear_arithmetic.

Fixpoint eval (x : la_term) (Γ : list nat) :=
  match x with
  | la_zero    => 0
  | la_one     => 1
  | la_var i   => nth i Γ 0
  | la_add x y => eval x Γ + eval y Γ
  end.

Definition Nat (a : la_atom) (Γ : list nat) :=
  match a with
  | la_eq x y => eval x Γ = eval y Γ
  | la_le x y => eval x Γ ≤ eval y Γ
  end.

Definition NatR (a : rel_atom) (Γ : list nat) :=
  let f := λ i, nth i Γ 0 in
  match a with
  | rel_zero i    => f i = 0
  | rel_one i     => f i = 1
  | rel_add i j k => f i + f j = f k
  | rel_eq i j    => f i = f j
  | rel_le i j    => f i ≤ f j
  end.

End Standard_models_of_linear_arithmetic.

(* Embedding formula in rformula. *)
Section Embedding_of_formula_in_rformula.

Fixpoint shift_vars n x :=
  match x with
  | la_zero    => la_zero
  | la_one     => la_one
  | la_var i   => la_var (n + i)
  | la_add x y => la_add (shift_vars n x) (shift_vars n y)
  end.

Notation "# i" := (la_var i) (at level 9, format "# i").
Notation "x << n" := (shift_vars n x) (at level 10, format "x << n").

Theorem eval_shift_vars x Γ n :
  eval (x<<n) Γ = eval x (skipn n Γ).
Proof.
induction x; simpl. 1,2: easy.
- revert Γ; induction n; simpl; intros.
  easy. destruct Γ; simpl. now destruct i. apply IHn.
- now rewrite IHx1, IHx2.
Qed.

Lemma reduce_la_term j x n :
  Σ ϕ, ∀Γ, Nat |= (la_eq #j (x<<n))[Γ] <-> NatR |= (ϕ)[Γ].
Proof.
revert j n; induction x; intros.
- now exists (rel_zero j).
- now exists (rel_one j).
- now exists (rel_eq j (n + i)).
- destruct (IHx1 0 (2 + n)) as [ϕ1 Hϕ1];
  destruct (IHx2 1 (2 + n)) as [ϕ2 Hϕ2].
  exists ∃[∃[rel_add 0 1 (2 + j) ∧` ϕ1 ∧` ϕ2]].
  simpl in *; split.
  + intros H. exists (eval (x2<<n) Γ), (eval (x1<<n) Γ).
    repeat split. easy.
    * apply Hϕ1; simpl. now rewrite ?eval_shift_vars.
    * apply Hϕ2; simpl. now rewrite ?eval_shift_vars.
  + intros [n2 [n1 [H [H1 H2]]]].
    apply Hϕ1 in H1; rewrite eval_shift_vars in H1;
    apply Hϕ2 in H2; rewrite eval_shift_vars in H2; simpl in *.
    rewrite ?eval_shift_vars; congruence.
Defined.

Lemma reduce_la_eq x y Γ :
  Nat |= (la_eq x y)[Γ] <-> 
  Nat |= (∃[la_eq #0 (x<<1) ∧` la_eq #0 (y<<1)])[Γ].
Proof.
split; simpl.
- intros H. exists (eval x Γ).
  split; now rewrite eval_shift_vars.
- intros [n [H1 H2]].
  rewrite eval_shift_vars in H1;
  rewrite eval_shift_vars in H2;
  simpl in *; congruence.
Qed.

Lemma reduce_la_le x y Γ :
  Nat |= (la_le x y)[Γ] <-> 
  Nat |= (∃[∃[la_le #0 #1 ∧` la_eq #0 (x<<2) ∧` la_eq #1 (y<<2)]])[Γ].
Proof.
split; simpl.
- intros H; exists (eval y Γ), (eval x Γ); repeat split.
  easy. all: now rewrite eval_shift_vars.
- intros [n2 [n1 [H [H1 H2]]]].
  rewrite eval_shift_vars in H1;
  rewrite eval_shift_vars in H2;
  simpl in *; congruence.
Qed.

Lemma la_le_iff_rel_le i j Γ :
  Nat |= (la_le #i #j)[Γ] <-> NatR |= (rel_le i j)[Γ].
Proof.
easy.
Qed.

Theorem convert_la_atom_to_rformula (a : la_atom) :
  Σ ϕ, ∀Γ, NatR |= (ϕ)[Γ] <-> Nat |= (a)[Γ].
Proof.
destruct a.
- (* Equality relation. *)
  destruct reduce_la_term with (j:=0)(x:=x)(n:=1) as [ϕx Hx];
  destruct reduce_la_term with (j:=0)(x:=y)(n:=1) as [ϕy Hy].
  eexists; symmetry; etransitivity. apply reduce_la_eq.
  apply Realizes_ex, Realizes_and; easy.
- (* Less or equal relation. *)
  destruct reduce_la_term with (j:=0)(x:=x)(n:=2) as [ϕx Hx].
  destruct reduce_la_term with (j:=1)(x:=y)(n:=2) as [ϕy Hy].
  eexists; symmetry; etransitivity. apply reduce_la_le.
  apply Realizes_ex, Realizes_ex, Realizes_and.
  apply la_le_iff_rel_le. apply Realizes_and; easy.
Defined.

Corollary convert_formula_to_rformula φ :
  Σ ϕ, ∀Γ, NatR |= (ϕ)[Γ] <-> Nat |= (φ)[Γ].
Proof.
induction φ.
- apply convert_la_atom_to_rformula.
- destruct IHφ as [ϕ H].
  exists (¬`ϕ); split; apply contra, H.
- destruct IHφ1 as [ϕ1 H1], IHφ2 as [ϕ2 H2].
  exists (ϕ1 ∧` ϕ2); split.
  all: split; [apply H1|apply H2]; apply H.
- destruct IHφ as [ϕ H].
  exists ∃[ϕ]; split;
  intros [x Hx]; exists x; apply H, Hx.
Defined.

End Embedding_of_formula_in_rformula.
