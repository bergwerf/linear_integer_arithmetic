(* Formulae and interpretations of Presburger arithmetic. *)

Require Import Utf8 List.
From larith Require Import tactics notations utilities.
Import ListNotations.

Section First_order_formulae.

Variable atom : Type.

(* Basic formula structure. *)
Inductive wff :=
  | WffAtom (a : atom)
  | WffAnd (φ ϕ : wff)
  | WffNot (φ : wff)
  | WffEx (i : nat) (φ : wff).

Variable domain : Type.
Variable Holds : (nat -> domain) -> atom -> Prop.

(* Standard formula interpretation. *)
Fixpoint Models (Γ : nat -> domain) (f : wff) :=
  match f with
  | WffAtom a   => Holds Γ a
  | WffAnd φ ϕ  => Models Γ φ /\ Models Γ ϕ
  | WffNot φ    => ¬Models Γ φ
  | WffEx i φ   => ∃x, Models (Γ;;i↦x) φ
  end.

End First_order_formulae.

Arguments Models {_ _}.
Notation "𝔄 |= ( φ )[ Γ ]" := (Models 𝔄 Γ φ)
  (at level 20, format "𝔄  |=  ( φ )[ Γ ]").

(* Atomic formulae for different languages. *)
Section Languages.

Inductive std_term :=
  | Zero
  | Succ (x : std_term)
  | Add (x y : std_term)
  | Var (i : nat).

Inductive std_atom :=
  | Std_eq (x y : std_term)
  | Std_le (x y : std_term).

Inductive r_atom :=
  | R_eq (i j : nat)
  | R_le (i j : nat)
  | R_add (i j k : nat)
  | R_const (i n : nat).

End Languages.

Notation formula := (wff std_atom).
Notation rformula := (wff r_atom).

Section Standard_models.

Fixpoint eval (Γ : nat -> nat) (x : std_term) :=
  match x with
  | Zero => 0
  | Succ y => S (eval Γ y)
  | Add x y => eval Γ x + eval Γ y
  | Var i => Γ i
  end.

Definition 𝔑 (Γ : nat -> nat) (a : std_atom) :=
  match a with
  | Std_eq x y => eval Γ x = eval Γ y
  | Std_le x y => eval Γ x <= eval Γ y
  end.

Definition 𝔑r (Γ : nat -> nat) (a : r_atom) :=
  match a with
  | R_eq i j => Γ i = Γ j
  | R_le i j => Γ i <= Γ j
  | R_add i j k => Γ i + Γ j = Γ k
  | R_const i n => Γ i = n
  end.

End Standard_models.

Section Embeddings.

Theorem convert_rformula_to_formula φ :
  Σ ϕ, ∀Γ, 𝔑r |= (φ)[Γ] <-> 𝔑 |= (ϕ)[Γ].
Proof.
Admitted.

End Embeddings.
