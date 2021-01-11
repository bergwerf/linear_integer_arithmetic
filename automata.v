(* Basic theory of automata. *)

Require Import Utf8 Bool PeanoNat List Lia.
From larith Require Import tactics notations lemmas.
Import ListNotations.

Record automaton (letter : Set) := Automaton {
  state : Type;
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

Fixpoint Accepts (word : list letter) (s : list (state A)) :=
  match word with
  | [] => existsb (accept A) s = true
  | c :: w => Accepts w (flat_map (trans A c) s)
  end.

Definition Language word := Accepts word [start A].
Definition Deterministic := ∀c s, length (trans A c s) = 1.
Definition Finite := Σ Q, ∀s : state A, In s Q.

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

Theorem not_Accepts_nil w :
  ¬Accepts w [].
Proof.
now induction w.
Qed.

Theorem Accepts_app w s s' :
  Accepts w (s ++ s') <-> Accepts w s \/ Accepts w s'.
Proof.
revert s s'; induction w as [|c w]; simpl; intros.
- split; rewrite existsb_app; intros; b_Prop; auto.
- split; intros.
  + apply IHw; rewrite <-flat_map_app; apply H.
  + rewrite flat_map_app; apply IHw, H.
Qed.

Theorem Accepts_reveal w s :
  Accepts w s -> Exists (Accepts w) (map (λ t, [t]) s).
Proof.
induction s; simpl; intros.
- exfalso; eapply not_Accepts_nil, H.
- replace (a :: s) with ([a] ++ s) in H by easy.
  apply Exists_cons; apply Accepts_app in H as [H|H].
  now left. right; apply IHs, H.
Qed.

End Definitions.

Arguments Accepts {_}.
Arguments Language {_}.
Arguments Deterministic {_}.
Arguments Finite {_}.

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
now rewrite prod_length, H1, H2.
Qed.

Theorem Prod_fin :
  Finite A -> Finite B -> Finite Prod.
Proof.
intros [a Ha] [b Hb]; exists (list_prod a b).
intros [x y]; apply in_prod. apply Ha. apply Hb.
Qed.

End Product_construction.

(* Automata can be made deterministic. *)
Section Powerset_construction.

Variable A : automaton letter.
Hypothesis fin : Finite A.
Hypothesis dec : ∀s t : state A, {s = t} + {s ≠ t}.

Definition Pow :
  automaton letter.
Proof.
apply Automaton with (state:=Σ l : list (state A), NoDup l).
- (* Initial state *)
  exists [start A].
  apply NoDup_cons. easy. apply NoDup_nil.
- (* Accepting states *)
  intros [s _]. apply (existsb (accept A) s).
- (* Transition *)
  intros c [s _].
  apply cons. 2: apply nil.
  exists (nodup dec (flat_map (trans A c) s)).
  apply NoDup_nodup.
Defined.

Theorem Pow_Accepts word s :
  Accepts Pow word s <-> Exists (Accepts A word) (map (@projT1 _ _) s).
Proof.
revert s; induction word as [|c w]; simpl; intros.
- split.
  + intros H; apply existsb_exists in H as [[x Hx] [H1 H2]].
    apply Exists_exists; exists x; split. 2: easy.
    apply in_map_iff; eexists; split. 2: apply H1. easy.
  + intros H; apply Exists_exists in H as [x [H1 H2]].
    apply in_map_iff in H1 as [xT [H1a H1b]].
    apply existsb_exists; exists xT; split. easy.
    destruct xT; simpl in *; subst; easy.
- split.
  + intros H; apply IHw, Exists_exists in H as [x [H1 Hx]].
    apply in_map_iff in H1 as [xT [H1 H2]].
    apply in_flat_map in H2 as [[x' Hx'] [H2 H3]].
    apply in_singleton in H3; subst. simpl in Hx.
    apply Exists_exists; exists x'; split.
    * apply in_map_iff; eexists; split. 2: apply H2. easy.
    * eapply Accepts_ext. apply Hx. intros. eapply nodup_In, H.
  + intros H; apply Exists_exists in H as [x [H1 H2]].
    apply in_map_iff in H1 as [xT Hx].
    remember (flat_map (trans A c)) as fm.
    apply IHw, Exists_exists; exists (nodup dec (fm x)); split.
    * apply in_map_iff;
      exists (existT _ (nodup dec (fm x)) (NoDup_nodup dec (fm x))).
      split; simpl. easy.
      apply in_flat_map; exists xT; split. easy.
      destruct xT, Hx; simpl in *; subst; now left.
    * eapply Accepts_ext. apply H2. intros; now apply nodup_In.
Qed.

Corollary Pow_spec word :
  Language Pow word <-> Language A word.
Proof.
split; intros H.
- apply Pow_Accepts in H; now inv H.
- apply Pow_Accepts. apply Exists_cons; now left.
Qed.

Theorem Pow_det :
  Deterministic Pow.
Proof.
intros c [s Hs]; easy.
Qed.

Theorem Pow_fin :
  Finite A -> Finite Pow.
Proof.
intros [a Ha].
(* We need to list all NoDup combinations of states. *)
Admitted.

End Powerset_construction.

(* We can direct missing transitions to a reject state. *)
Section Explicit_rejection.

Variable A : automaton letter.

Definition Opt_accept s :=
  match s with
  | None => false
  | Some s' => accept A s'
  end.

Definition Opt_trans c s :=
  match s with
  | None => [None]
  | Some s' =>
    let t := trans A c s' in
    if length t =? 0
    then [None]
    else map Some t
  end.

Definition Opt := Automaton _ _ (Some (start A)) Opt_accept Opt_trans.

Theorem Opt_Accepts word s :
  Accepts Opt word s <-> Accepts A word (remove_None s).
Proof.
revert s; induction word as [|c w]; simpl; intros.
- (* To avoid needing decidability over (state A), we use induction again. *)
  induction s as [|[a|] s]; simpl. easy. 2: apply IHs.
  split; intros; b_Prop.
  1,3: now left. 1,2: right; now apply IHs.
- replace (flat_map (trans A c) (remove_None s))
  with (remove_None (flat_map (Opt_trans c) s)). apply IHw.
  induction s as [|[a|] s]; simpl. easy. 2: apply IHs.
  remember (trans A c a) as t; destruct t; simpl. apply IHs.
  now rewrite remove_None_app, remove_None_map_Some, IHs.
Qed.

Corollary Opt_spec word :
  Language Opt word <-> Language A word.
Proof.
intros; apply Opt_Accepts.
Qed.

Theorem Opt_det :
  (∀c s, length (trans A c s) <= 1) -> Deterministic Opt.
Proof.
intros H c [s|]; simpl. 2: easy.
destruct (length (trans A c s) =? 0) eqn:E; simpl; b_Prop.
easy. assert(Hcs := H c s). rewrite map_length; lia.
Qed.

Theorem Opt_fin :
  Finite A -> Finite Opt.
Proof.
intros [a Ha]; exists (None :: map Some a); intros [s|].
- apply in_cons. apply in_map_iff; exists s; split. easy. apply Ha.
- apply in_eq.
Qed.

End Explicit_rejection.

(* Regular languages are closed under complementation. *)
Section Complementation.

Variable A : automaton letter.
Hypothesis det : Deterministic A.

Definition Compl := Automaton _ _
  (start A) (λ s, negb (accept A s)) (trans A).

Theorem Compl_Accepts word s :
  Accepts Compl word [s] <-> ¬Accepts A word [s].
Proof.
revert s; induction word as [|c w]; simpl; intros.
- now destruct (accept A s).
- rewrite app_nil_r. assert(H := det c s).
  apply list_singleton in H as [x R]; rewrite R.
  apply IHw.
Qed.

Corollary Compl_spec word :
  Language Compl word <-> ¬Language A word.
Proof.
intros; apply Compl_Accepts.
Qed.

Theorem Compl_det :
  Deterministic Compl.
Proof.
easy.
Qed.

Theorem Compl_fin :
  Finite A -> Finite Compl.
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

(* The pre-image of a word in the image. *)
Definition Pre_image word pre :=
  length pre = length word /\ Forall2 (@In letter) pre (map proj word).

Theorem Proj_Accepts word s :
  Accepts Proj word s <-> ∃pre, Pre_image word pre /\ Accepts A pre s.
Proof.
revert s; induction word as [|c w]; simpl; intros.
- split.
  + exists []; repeat split; simpl; easy.
  + intros [w [[H1 H2] H3]]. apply length_zero_iff_nil in H1; now subst.
- split.
  + intros. apply IHw in H as [v [[H1 H2] H3]].
    apply Accepts_reveal, Exists_exists in H3 as [xs [H4 H5]].
    apply in_map_iff in H4 as [x [R Hx]]; subst.
    apply in_flat_map in Hx as [x' [Hx' Hx]].
    apply in_flat_map in Hx as [c' Hc'].
    exists (c' :: v); repeat split; simpl.
    * now rewrite H1.
    * apply Forall2_cons; easy.
    * eapply Accepts_ext. apply H5. intros y Hy. inv Hy; try easy.
      apply in_flat_map; exists x'; easy.
  + intros [v [[H1 H2] H3]]. destruct v; simpl in *. easy.
    inv H2. apply IHw; exists v; repeat split. lia. easy.
    eapply Accepts_ext. apply H3. intros x Hx.
    apply in_flat_map in Hx as [x' Hx].
    apply in_flat_map; exists x'; split. easy.
    apply in_flat_map; exists l; easy.
Qed.

Corollary Proj_spec word :
  Language Proj word <-> ∃pre, Pre_image word pre /\ Language A pre.
Proof.
intros; apply Proj_Accepts.
Qed.

Theorem Proj_fin :
  Finite A -> Finite Proj.
Proof.
easy.
Qed.

End Projection.

(* We can find a word in any regular language or decide it is empty. *)
(* The automaton must have a finite number of states. *)
(* A more complete proof would construct regular expressions. *)
Section Decidability.

Variable A : automaton letter.
Hypothesis fin : Finite A.

Theorem Language_empty_dec :
  {∃w, Language A w} + {∀w, ¬Language A w}.
Proof.
(* Well-founded induction on the number of states. *)
(* - Turn predecessors of accept states into accept states. *)
(* - Remove all old accept states. *)
(* - We either reach the start state, or run out of accept states. *)
Admitted.

End Decidability.

End Results.
