(* Basic theory of automata. *)

Require Import Utf8 Bool PeanoNat List Lia.
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

Section Definitions.

Variable letter : Set.
Variable A : automaton letter.

Definition Deterministic := ∀c s, length (trans A c s) <= 1.
Definition Explicit := ∀c s, length (trans A c s) > 0.

Fixpoint Accepts (word : list letter) (s : list (state A)) :=
  match word with
  | [] => existsb (accept A) s = true
  | c :: w => Accepts w (flat_map (trans A c) s)
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

Definition Language word := Accepts word [start A].

End Definitions.

Arguments Deterministic {_}.
Arguments Explicit {_}.
Arguments Accepts {_}.
Arguments Language {_}.

Section Results.

Variable letter : Set.

(* Regular languages are closed under taking intersections. *)
(* Two automatons are simulated simultaneously. *)
Section Product_construction.

Variable A B : automaton letter.

Definition prod_start := (start A, start B).
Definition prod_accept s := accept A (fst s) && accept B (snd s).
Definition prod_trans c s := list_prod (trans A c (fst s)) (trans B c (snd s)).
Definition Prod := Automaton _ _ prod_start prod_accept prod_trans.

Theorem Prod_Accepts word sa sb :
  Accepts A word sa /\ Accepts B word sb <->
  Accepts Prod word (list_prod sa sb).
Proof.
revert sa sb; induction word as [|c w]; simpl; intros.
- split.
  + intros [Ha Hb];
    apply existsb_exists in Ha as [x Hx];
    apply existsb_exists in Hb as [y Hy].
    apply existsb_exists; exists (x, y); split.
    * now apply in_prod.
    * unfold prod_accept; simpl; now b_Prop.
  + intros H.
    apply existsb_exists in H as [[x y] [H1 H2]].
    apply in_prod_iff in H1. unfold prod_accept in H2; simpl in H2; b_Prop.
    split; apply existsb_exists. now exists x. now exists y.
- split; intros.
  + eapply Accepts_ext. apply IHw, H.
    intros [x y] H'. apply in_prod_iff in H' as [H1 H2].
    apply in_flat_map in H1 as [x' Hx'];
    apply in_flat_map in H2 as [y' Hy'].
    apply in_flat_map; exists (x', y'); split.
    now apply in_prod. unfold prod_trans; simpl. now apply in_prod.
  + apply IHw; eapply Accepts_ext. apply H. intros [x y] H'.
    apply in_flat_map in H' as [[x' y'] [H1 H2]].
    unfold prod_trans in H2; simpl in H2.
    apply in_prod_iff in H1; apply in_prod_iff in H2.
    apply in_prod; apply in_flat_map.
    now exists x'. now exists y'.
Qed.

Corollary Prod_spec word :
  Language A word /\ Language B word <-> Language Prod word. 
Proof.
apply Prod_Accepts.
Qed.

Theorem Prod_det :
  Deterministic A -> Deterministic B -> Deterministic Prod.
Proof.
intros H1 H2 c [x y].
simpl; unfold prod_trans; simpl.
destruct (list_length_le_1 _ (H1 c x)) as [Hx|[x' Hx]];
destruct (list_length_le_1 _ (H2 c y)) as [Hy|[y' Hy]];
rewrite Hx, Hy; simpl; lia.
Qed.

Theorem Prod_explicit :
  Explicit A -> Explicit B -> Explicit Prod.
Proof.
intros H1 H2 c [x y].
simpl; unfold prod_trans; simpl.
assert(Hx := H1 c x); assert (Hy := H2 c y).
rewrite prod_length; lia.
Qed.

End Product_construction.

(* Automata can be made deterministic. *)
Section Powerset_construction.

Variable A : automaton letter.

Definition pow_start := [start A].
Definition pow_accept s := existsb (accept A) s.
Definition pow_trans c s := [flat_map (trans A c) s].
Definition Pow := Automaton _ _ pow_start pow_accept pow_trans.

Theorem Pow_Accepts word s :
  Accepts Pow word s <-> Exists (Accepts A word) s.
Proof.
revert s; induction word as [|c w]; simpl; intros.
- split.
  + intros H; apply existsb_exists in H as [x H].
    apply Exists_exists; now exists x.
  + intros H; apply Exists_exists in H as [x H].
    apply existsb_exists; now exists x.
- split.
  + intros H; apply IHw, Exists_exists in H as [x [H1 H2]].
    apply in_flat_map in H1 as [x' [H1 H3]].
    inv H3. apply Exists_exists; now exists x'. easy.
  + intros H; apply Exists_exists in H as [x H].
    apply IHw, Exists_exists; exists (flat_map (trans A c) x); split.
    * apply in_flat_map; exists x; split. easy. apply in_eq.
    * easy.
Qed.

Corollary Pow_spec word :
  Language Pow word <-> Language A word.
Proof.
split; intros H.
- apply Pow_Accepts in H; now inv H.
- apply Pow_Accepts. apply Exists_cons; now left.
Qed.

Theorem Pow_det :
  Deterministic Pow /\ Explicit Pow.
Proof.
split. easy. intros c s; simpl; lia.
Qed.

End Powerset_construction.

(* We can direct missing transitions to a reject state. *)
Section Explicit_rejection.

Variable A : automaton letter.

Definition Erej_accept s :=
  match s with
  | None => false
  | Some s' => accept A s'
  end.

Definition Erej_trans c s :=
  match s with
  | None => [None]
  | Some s' =>
    let t := trans A c s' in
    if length t =? 0
    then [None]
    else map Some t
  end.

Definition Erej := Automaton _ _ (Some (start A)) Erej_accept Erej_trans.

Theorem Erej_Accepts word s :
  Accepts Erej word s <-> Accepts A word (remove_None s).
Proof.
revert s; induction word as [|c w]; simpl; intros.
- (* To avoid needing decidability over (state A), we use induction again. *)
  induction s as [|[a|] s]; simpl. easy. 2: apply IHs.
  split; intros; b_Prop.
  1,3: now left. 1,2: right; now apply IHs.
- replace (flat_map (trans A c) (remove_None s))
  with (remove_None (flat_map (Erej_trans c) s)). apply IHw.
  induction s as [|[a|] s]; simpl. easy. 2: apply IHs.
  remember (trans A c a) as t; destruct t; simpl. apply IHs.
  now rewrite remove_None_app, remove_None_map_Some, IHs.
Qed.

Corollary Erej_spec word :
  Language Erej word <-> Language A word.
Proof.
intros; apply Erej_Accepts.
Qed.

Theorem Erej_explicit :
  Explicit Erej.
Proof.
intros c [s|]; simpl. destruct (trans A c s); simpl; lia. lia.
Qed.

Theorem Erej_det :
  Deterministic A -> Deterministic Erej.
Proof.
intros H c [s|]; simpl. 2: easy.
destruct (length (trans A c s)); simpl. easy.
rewrite map_length; apply H.
Qed.

End Explicit_rejection.

(* Regular languages are closed under complementation. *)
Section Complementation.

Variable A : automaton letter.
Hypothesis det : Deterministic A.
Hypothesis explicit : Explicit A.

Definition Compl := Automaton _ _
  (start A) (λ s, negb (accept A s)) (trans A).

Theorem Compl_Accepts word s :
  Accepts Compl word [s] <-> ¬Accepts A word [s].
Proof.
revert s; induction word as [|c w]; simpl; intros.
- now destruct (accept A s).
- rewrite app_nil_r.
  assert(H1 := det c s);
  assert(H2 := explicit c s).
  destruct (trans A c s) as [|s' none]. easy.
  destruct none. apply IHw. simpl in H1; lia.
Qed.

Corollary Compl_spec word :
  Language Compl word <-> ¬Language A word.
Proof.
intros; apply Compl_Accepts.
Qed.

Theorem Compl_det :
  Deterministic Compl /\ Explicit Compl.
Proof.
easy.
Qed.

End Complementation.

(* A language using a different alphabet can be decided using a projection. *)
Section Projection.

Variable A : automaton letter.
Variable image : Set.
Variable proj : image -> list letter.

Definition Proj_trans i s := flat_map (λ c, trans A c s) (proj i).
Definition Proj := Automaton image _ (start A) (accept A) Proj_trans.

Theorem Proj_Accepts word s :
  Accepts Proj word s <->
  ∃pre, length pre = length word /\ Accepts A pre s /\
  Forall2 (@In letter) pre (map proj word).
Proof.
revert s; induction word as [|c w]; simpl; intros.
- split.
  + exists []; simpl; repeat split; easy.
  + intros [w [H1 H2]]. apply length_zero_iff_nil in H1; now subst.
- split.
  + intros. apply IHw in H as [v [H1 [H2 H3]]].
    (* We need to find out under which state the accepting path proceeds. *)
    admit.
  + intros [v [H1 [H2 H3]]]. destruct v; simpl in *. easy.
    inv H3. apply IHw; exists v; repeat split. lia.
    * eapply Accepts_ext. apply H2. intros x Hx.
      apply in_flat_map in Hx as [x' Hx].
      apply in_flat_map; exists x'; split. easy.
      apply in_flat_map; exists l; easy.
    * easy.
Admitted.

End Projection.

End Results.
