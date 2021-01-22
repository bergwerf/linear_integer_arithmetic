(* Decision procedures for linear integer arithmetic. *)

Require Vector.
Require Import Utf8 Nat BinNat List.
From larith Require Import tactics notations utilities.
From larith Require Import formulae automata.
Import ListNotations.

(* Definition of a regular predicate. *)
Section Regular_predicates.

Section Regular_definition.

Variable letter : Set.
Variable P : list letter -> Prop.

(* P is regular iff its domain can be decided using a DFA. *)
Record regular := Regular {
  r_automaton : automaton letter;
  r_det       : Deterministic r_automaton;
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
destruct is_regular as [A _ n size dec spec].
eapply dec_replace. apply spec.
eapply Language_inhabited_dec.
apply full_alphabet. apply dec. apply size.
Qed.

End Regular_definition.

(* Replace predicate with an equivalent one. *)
Theorem regular_ext {letter} P Q :
  regular letter P -> (∀w, P w <-> Q w) -> regular letter Q.
Proof.
intros [A det size fin dec spec] H.
eapply Regular with (r_automaton:=A).
apply det. apply fin. apply dec.
intros; rewrite <-H; apply spec.
Qed.

(* Change the domain alphabet. *)
Theorem regular_proj {letter letter'} P Q f :
  regular letter P -> (∀w, P (map f w) <-> Q w) -> regular letter' Q.
Proof.
intros [A det size fin dec spec] H.
pose(B := Automata.proj _ A _ (λ c, [f c])).
eapply Regular with (r_automaton:=B).
- apply Automata.proj_det; easy.
- apply Automata.proj_size, fin.
- apply dec.
- intros. rewrite <-H, <-spec.
  unfold B; rewrite Automata.proj_spec.
  unfold Automata.Image; rewrite map_map_singleton. split.
  + intros [v [H1 H2]]. apply Forall2_In_singleton in H1; congruence.
  + intros Hfw; exists (map f w); split.
    now apply Forall2_In_singleton. easy.
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
Fixpoint transpose {n} (mat : list (Vector.t T n)) : Vector.t (list T) n :=
  match mat with
  | []     => Vector.const [] n
  | v :: m => Vector.map2 cons v (transpose m)
  end.

Theorem transpose_cons {n} (mat : list (Vector.t T (S n))) :
  transpose mat = map Vector.hd mat ;; transpose (map Vector.tl mat).
Proof.
induction mat; simpl. easy.
apply Vector.caseS' with (v:=a).
intros; now rewrite IHmat.
Qed.

Theorem transpose_nth {n} (mat : list (Vector.t T n)) (i : Fin.t n)  :
  Vector.nth (transpose mat) i = map (λ v, Vector.nth v i) mat.
Proof.
induction mat; simpl. now induction i.
rewrite <-IHmat. apply Vector_nth_map2_cons.
Qed.

End Matrix_transposition.

Arguments transpose {_ _}.

(* Algorithm for deciding first-order realizability using finite automata. *)
Section Decide_wff_using_automata.

Variable atom domain : Type. 
Variable value : list bool -> domain.
Variable Model : model atom domain.

Definition vctx {n} (w : list (vec n)) : list domain :=
  Vector.to_list (Vector.map value (transpose w)).

Lemma vctx_nth {n} (w : list (vec n)) i d :
  nth (findex i) (vctx w) d = value (Vector.nth (transpose w) i).
Proof.
unfold vctx. rewrite Vector_nth_to_list. apply Vector_nth_map.
Qed.

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
