(* Decision procedures for linear integer arithmetic. *)

Require Vector.
Require Import Utf8 Nat BinNat List.
From larith Require Import tactics notations utilities.
From larith Require Import formulae automata.
Import ListNotations.

(* Definition of a regular predicate. *)
Section Regular_predicates.

Variable letter : Set.
Variable P : list letter -> Prop.

Record regular := Regular {
  r_automaton : automaton letter;
  r_size      : nat;
  r_finite    : Finite r_automaton r_size;
  r_dec       : ∀s t : state r_automaton, {s = t} + {s ≠ t};
  r_spec      : ∀w, Language r_automaton w <-> P w;
}.

(* Regular predicates over a finite alphabet can be decided. *)
Variable alphabet : list letter.
Hypothesis full_alphabet : ∀c, In c alphabet.
Hypothesis is_regular : regular.

Theorem regular_dec :
  {∃w, P w} + {∀w, ¬P w}.
Proof.
destruct is_regular as [A n size dec spec].
eapply dec_replace. apply spec.
eapply Language_inhabited_dec.
apply full_alphabet. apply dec. apply size.
Qed.

End Regular_predicates.

(* Finite-length vectors form a finite alphabet. *)
Section Finite_vector_alphabet.

Fixpoint enumerate_vectors n : list (vec n) :=
  match n with
  | 0 => [⟨⟩]
  | S m =>
    let vs := enumerate_vectors m in
    map (vcons false m) vs ++
    map (vcons true m) vs
  end.

Theorem enumerate_vectors_spec n (v : vec n) :
  In v (enumerate_vectors n).
Proof.
induction v; simpl. now left.
apply in_app_iff; destruct h; [right|left]; apply in_map, IHv.
Qed.

End Finite_vector_alphabet.

(* Transpose a vector list. *)
Section Matrix_transposition.

Variable T : Type.

(* Convert from a list of collumn vectors to a vector of row lists. *)
Fixpoint transpose {n} (w : list (Vector.t T n)) : Vector.t (list T) n :=
  match w with
  | [] => Vector.const [] n
  | v :: w' => Vector.map2 cons v (transpose w')
  end.

Theorem transpose_cons {n} (w : list (Vector.t T (S n))) :
  transpose w = map Vector.hd w ;; transpose (map Vector.tl w).
Proof.
induction w; simpl. easy.
apply Vector.caseS' with (v:=a).
intros; now rewrite IHw.
Qed.

End Matrix_transposition.

Arguments transpose {_ _}.

(* Algorithm for deciding first-order realizability using finite automata. *)
Section Decide_wff_using_automata.

Variable atom domain : Type. 
Variable value : list bool -> domain.
Variable Model : model atom domain.

Definition vctx {n} (w : list (vec n)) : list domain :=
  map value (Vector.to_list (transpose w)).

Hypothesis hypothesis :
  ∀a, Σ n, regular (vec n) (λ w, Model (vctx w) a).

Theorem wff_regular φ :
  Σ n, regular (vec n) (λ w, Model |= (φ)[vctx w]).
Proof.
induction φ; simpl.
- (* Atomic formulae: we assume these are regular. *)
  apply hypothesis.
- (* Conjunction: project on a common alphabet, and use the product. *)
  admit.
- (* Negation: apply determinization and use the complement. *)
  admit.
- (* Quantification: use tail projection, and find a witness in the image. *)
  admit.
Abort.

End Decide_wff_using_automata.
