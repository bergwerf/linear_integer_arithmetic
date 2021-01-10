(* Basic theory of automata. *)

Require Import Utf8 Bool List.
From larith Require Import tactics notations lemmas.
Import ListNotations.

Record automaton (letter : Set) := Automaton {
  state : Set;
  start : state;
  accept : state -> bool;
  trans : letter -> state -> list state;
}.

Arguments state {_}.
Arguments start {_}.
Arguments accept {_}.
Arguments trans {_}.

Section Simulation.

Variable letter : Set.
Variable a : automaton letter.

Fixpoint Accepts (word : list letter) (s : list (state a)) :=
  match word with
  | [] => existsb (accept a) s = true
  | l :: w => Accepts w (flat_map (trans a l) s)
  end.

Theorem Accepts_dec w s :
  {Accepts w s} + {¬Accepts w s}.
Proof.
revert s; induction w; simpl; intros.
apply bool_dec. apply IHw.
Qed.

Theorem Accepts_ext w s1 s2 :
  Accepts w s1 -> (∀s, In s s1 -> In s s2) -> Accepts w s2.
Proof.
revert s1 s2; induction w; simpl; intros.
- apply existsb_exists in H as [s Hs].
  apply existsb_exists; exists s; split. apply H0, Hs. apply Hs.
- eapply IHw. apply H.
  intros; apply in_flat_map_Exists, Exists_exists in H1 as [s' Hs'].
  apply in_flat_map_Exists, Exists_exists; exists s'; split.
  apply H0, Hs'. apply Hs'.
Qed.

Definition Language word := Accepts word [start a].

End Simulation.

Arguments Accepts {_}.
Arguments Language {_}.

Section Conjunction.

Variable letter : Set.
Variable a b : automaton letter.

Definition conj_start := (start a, start b).
Definition conj_accept s := accept a (fst s) && accept b (snd s).
Definition conj_trans l s := list_prod (trans a l (fst s)) (trans b l (snd s)).
Definition conj := Automaton letter _ conj_start conj_accept conj_trans.

Theorem conj_accepts word sa sb :
  Accepts a word sa /\ Accepts b word sb <->
  Accepts conj word (list_prod sa sb).
Proof.
revert sa sb; induction word as [|l w]; simpl; intros.
- split.
  + intros [Ha Hb];
    apply existsb_exists in Ha as [x Hx];
    apply existsb_exists in Hb as [y Hy].
    apply existsb_exists; exists (x, y); split.
    * now apply in_prod.
    * unfold conj_accept; simpl; now b_Prop.
  + intros H.
    apply existsb_exists in H as [[x y] [H1 H2]].
    apply in_prod_iff in H1. unfold conj_accept in H2; simpl in H2; b_Prop.
    split; apply existsb_exists. now exists x. now exists y.
- split; intros.
  + eapply Accepts_ext. apply IHw, H.
    intros [x y] H'. apply in_prod_iff in H' as [H1 H2].
    apply in_flat_map_Exists, Exists_exists in H1 as [x' Hx'];
    apply in_flat_map_Exists, Exists_exists in H2 as [y' Hy'].
    apply in_flat_map_Exists, Exists_exists; exists (x', y'); split.
    now apply in_prod. unfold conj_trans; simpl. now apply in_prod.
  + apply IHw; eapply Accepts_ext. apply H. intros [x y] H'.
    apply in_flat_map_Exists, Exists_exists in H' as [[x' y'] [H1 H2]].
    unfold conj_trans in H2; simpl in H2.
    apply in_prod_iff in H1; apply in_prod_iff in H2.
    apply in_prod; apply in_flat_map_Exists, Exists_exists.
    now exists x'. now exists y'.
Qed.

Corollary conj_spec word :
  Language a word /\ Language b word <-> Language conj word.
Proof.
apply conj_accepts.
Qed.

End Conjunction.
