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
  r_dfa    : automaton letter;
  r_det    : Deterministic r_dfa;
  r_size   : nat;
  r_finite : Finite r_dfa r_size;
  r_dec    : ∀s t : state r_dfa, {s = t} + {s ≠ t};
  r_spec   : ∀w, Language r_dfa w <-> P w;
}.

(* Regular predicates over a finite alphabet can be decided. *)
Variable alphabet : list letter.
Hypothesis full_alphabet : ∀c, In c alphabet.
Hypothesis is_regular : regular.

Theorem regular_dec :
  {∃w, P w} + {∀w, ¬P w}.
Proof.
destruct is_regular as [A _ n size dec spec].
edestruct Language_inhabited_dec with (A:=A).
apply full_alphabet. apply dec. apply size.
- left; destruct e as [w H]; exists w; apply spec, H.
- right; intros; rewrite <-spec; apply n0.
Defined.

End A_regular_predicate.

Arguments regular {_}.

(* Replace predicate with an equivalent one. *)
Theorem regular_ext {letter : Set} (P Q : list letter -> Prop) :
  regular P -> (∀w, P w <-> Q w) -> regular Q.
Proof.
intros [A det size fin dec spec] H.
eapply Regular with (r_dfa:=A).
apply det. apply fin. apply dec.
intros; rewrite <-H; apply spec.
Defined.

(* Change the domain alphabet. *)
Theorem regular_proj {letter letter' : Set} P Q (pr : letter' -> letter) :
  regular P -> (∀w, P (map pr w) <-> Q w) -> regular Q.
Proof.
intros [A det size fin dec spec] H.
pose(B := Automata.proj _ A _ (λ c, [pr c])).
eapply Regular with (r_dfa:=B).
- apply Automata.proj_det; easy.
- apply fin.
- apply dec.
- intros. rewrite <-H, <-spec.
  unfold B; rewrite Automata.proj_spec.
  unfold Automata.Image; rewrite map_map_singleton. split.
  + intros [v [H1 H2]]. apply Forall2_In_singleton in H1; congruence.
  + intros Hfw; exists (map pr w); split.
    now apply Forall2_In_singleton. easy.
Defined.

Section Closure_under_logical_operations.

Variable letter : Set.
Variable P Q : list letter -> Prop.

Theorem regular_conjunction :
  regular P -> regular Q -> regular (λ w, P w /\ Q w).
Proof.
intros [A detA sizeA finA decA specA] [B detB sizeB finB decB specB].
eapply Regular with (r_dfa:=Automata.prod _ A B).
- now apply Automata.prod_det.
- apply Automata.prod_size. apply finA. apply finB.
- intros [s s'] [t t']. destruct (decA s t), (decB s' t'); subst.
  now left. all: right; intros H; inv H.
- intros; rewrite Automata.prod_spec, specA, specB; reflexivity.
Defined.

Theorem regular_negation :
  regular P -> regular (λ w, ¬P w).
Proof.
intros [A det size fin dec spec].
eapply Regular with (r_dfa:=Automata.compl _ A).
- apply Automata.compl_det, det.
- apply fin.
- apply dec.
- intros. rewrite Automata.compl_spec.
  split; apply contra, spec. easy.
Defined.

End Closure_under_logical_operations.

End Regularity.
Export Regularity.
