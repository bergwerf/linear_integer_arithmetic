(* Decision procedures for linear integer arithmetic. *)

Require Import Utf8 List.
From larith Require Import tactics notations utilities automata.
Import ListNotations.

(* Definition of a regular predicate. *)
Module Regularity.

Section A_regular_predicate.

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

End A_regular_predicate.

Arguments regular {_}.

(* Replace predicate with an equivalent one. *)
Theorem regular_ext {letter : Set} (P Q : list letter -> Prop) :
  regular P -> (∀w, P w <-> Q w) -> regular Q.
Proof.
intros [A det size fin dec spec] H.
eapply Regular with (r_automaton:=A).
apply det. apply fin. apply dec.
intros; rewrite <-H; apply spec.
Qed.

(* Change the domain alphabet. *)
Theorem regular_proj {letter letter' : Set} P Q (f : letter' -> letter) :
  regular P -> (∀w, P (map f w) <-> Q w) -> regular Q.
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

Section Regular_operations.

Variable letter : Set.
Variable P Q : list letter -> Prop.

Theorem regular_conj :
  regular P -> regular Q -> regular (λ w, P w /\ Q w).
Proof.
Admitted.

Theorem regular_neg :
  regular P -> regular (λ w, ¬P w).
Proof.
intros [A det size fin dec spec].
eapply Regular with (r_automaton:=Automata.compl _ A).
apply Automata.compl_det, det. now apply Automata.compl_size, fin. apply dec.
intros. rewrite Automata.compl_spec. split; apply contra, spec. easy.
Qed.

End Regular_operations.

End Regularity.
Export Regularity.
