(* A carrier type for regular predicates. *)

From larith Require Import A_setup B1_utils C1_sort C3_order D1_automaton.

Section A_regular_predicate.

Variable letter : Set.
Variable P : list letter -> Prop.

(* P is regular iff its domain can be decided using a finite automaton. *)
(* An optional proof of determinism may be provided (for optimization). *)
(* We also request that the automaton states are comparable. *)
Record regular := Regular {
  r_fsa    : automaton letter;
  r_size   : nat;
  r_finite : Finite r_fsa r_size;
  r_spec   : ∀w, Language r_fsa w <-> P w;
  r_det    : option (Deterministic r_fsa);
  r_cmp    : state r_fsa -> state r_fsa -> comparison;
  r_ord    : Order r_cmp;
}.

(* Regular predicates over a finite alphabet can be decided. *)
Variable alphabet : list letter.
Hypothesis full_alphabet : ∀c, In c alphabet.
Hypothesis is_regular : regular.

Theorem regular_dec :
  (Σ w, P w) + {∀w, ¬P w}.
Proof.
destruct is_regular as [A size fin spec _ cmp ord].
edestruct Language_inhabited_dec with (A:=A).
apply full_alphabet. eapply cmp_dec, ord. apply fin.
- left; destruct s as [w H]; exists w; apply spec, H.
- right; intros; rewrite <-spec; apply n.
Defined.

End A_regular_predicate.

Arguments regular {_}.

(* Replace predicate with an equivalent one. *)
Theorem regular_ext {letter : Set} (P Q : list letter -> Prop) :
  regular P -> (∀w, P w <-> Q w) -> regular Q.
Proof.
intros [A size fin spec det cmp ord] H.
eapply Regular with (r_fsa:=A). apply fin.
intros; rewrite <-H; apply spec. apply det. apply ord.
Defined.

(* Change the alphabet. *)
Theorem regular_proj {letter letter' : Set} P Q (pr : letter' -> letter) :
  regular P -> (∀w, P (map pr w) <-> Q w) -> regular Q.
Proof.
intros [A size fin spec det cmp ord] H.
pose(B := Automata.proj _ A _ (λ c, [pr c])).
eapply Regular with (r_fsa:=B).
- apply fin.
- intros. rewrite <-H, <-spec.
  unfold B; rewrite Automata.proj_spec.
  unfold Automata.Image; rewrite map_map_singleton. split.
  + intros [v [H1 H2]]. apply Forall2_In_singleton in H1; congruence.
  + intros Hfw; exists (map pr w); split.
    now apply Forall2_In_singleton. easy.
- destruct det.
  + apply Some, Automata.proj_det; [apply d|easy].
  + apply None.
- apply ord.
Defined.

Section Closure_under_logical_operations.

Variable letter : Set.
Variable P Q : list letter -> Prop.

Theorem regular_conjunction :
  regular P -> regular Q -> regular (λ w, P w /\ Q w).
Proof.
intros [A sizeA finA specA detA cmpA ordA];
intros [B sizeB finB specB detB cmpB ordB].
eapply Regular with (r_fsa:=Automata.prod _ A B)(r_cmp:=cmp_pair _ _ cmpA cmpB).
- apply Automata.prod_size. apply finA. apply finB.
- intros; rewrite Automata.prod_spec, specA, specB; reflexivity.
- destruct detA, detB. apply Some, Automata.prod_det; easy. all: apply None.
- apply Order_pair; easy.
Defined.

Theorem regular_negation :
  regular P -> regular (λ w, ¬P w).
Proof.
intros [A size fin spec [det|] cmp ord].
- (* A is deterministic. *)
  eapply Regular with (r_fsa:=Automata.compl _ A).
  + apply fin.
  + intros; etransitivity.
    apply Automata.compl_spec, det.
    split; apply contra, spec.
  + apply Some, det.
  + apply ord.
- (* A is not deterministic; use the powerset construction. *)
  pose(leb := cmp_leb _ cmp);
  assert(Hleb := Linear_order_cmp_leb _ cmp ord);
  assert(dec := cmp_dec cmp ord).
  eapply Regular with (r_fsa:=Automata.compl _ (Automata.pow _ A leb Hleb)).
  + apply Automata.pow_size. apply dec. apply fin.
  + intros; etransitivity.
    apply Automata.compl_spec, Automata.pow_det.
    rewrite Automata.pow_spec.
    split; apply contra, spec.
  + apply Some, Automata.pow_det.
  + eapply Order_sig. apply Order_list, ord.
    apply Automata.pow_state_pir, dec.
Qed.

End Closure_under_logical_operations.
