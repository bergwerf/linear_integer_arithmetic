(* Basic theory of automata. *)

Require Import Utf8 Bool PeanoNat Wf_nat List Lia.
From larith Require Import tactics notations utilities.
Import ListNotations.

Record automaton (letter : Set) := Automaton {
  state  : Set;
  start  : state;
  accept : state -> bool;
  trans  : letter -> state -> list state;
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

(* The language of an automaton contains all accepted words. *)
Definition Language word := Accepts word [start A].

(* An automaton is deterministic if every transition goes to 1 state. *)
Definition Deterministic := ∀c s, length (trans A c s) = 1.

(* Two state lists are considered similar if they accept the same strings. *)
Definition Similar s t := ∀w, Accepts w s <-> Accepts w t.

(* A finite automaton has a list of all states up to similarity. *)
(* There is an effective procedure to point out a canonical state. *)
Definition Finite n := Σ Q, (length Q = n) ×
  (∀s : state A, Σ can, In can Q /\ Similar [s] [can]).

Theorem not_Accepts_nil w :
  ¬Accepts w [].
Proof.
now induction w.
Qed.

Theorem Accepts_dec w s :
  {Accepts w s} + {¬Accepts w s}.
Proof.
revert s; induction w; simpl; intros.
apply bool_dec. apply IHw.
Qed.

Theorem Accepts_subset w s1 s2 :
  Accepts w s1 -> (∀s, In s s1 -> In s s2) -> Accepts w s2.
Proof.
revert s1 s2; induction w; simpl; intros.
- apply existsb_exists in H as [s Hs].
  apply existsb_exists; exists s; split. apply H0, Hs. apply Hs.
- eapply IHw. apply H.
  intros; apply in_flat_map_Exists, Exists_exists in H1 as [t Ht].
  apply in_flat_map_Exists, Exists_exists; exists t; split.
  apply H0, Ht. apply Ht.
Qed.

Theorem Accepts_app w s t :
  Accepts w (s ++ t) <-> Accepts w s \/ Accepts w t.
Proof.
revert s t; induction w as [|c w]; simpl; intros.
- split; rewrite existsb_app; intros; b_Prop; auto.
- split; intros.
  + apply IHw; rewrite <-flat_map_app; apply H.
  + rewrite flat_map_app; apply IHw, H.
Qed.

Theorem Accepts_determine w s :
  Accepts w s -> ∃t, In t s /\ Accepts w [t].
Proof.
induction s; simpl; intros.
- exfalso; eapply not_Accepts_nil, H.
- replace (a :: s) with ([a] ++ s) in H by easy.
  apply Accepts_app in H as [H|H].
  + exists a; split. now left. easy.
  + apply IHs in H as [t Ht]; exists t; split. now right. easy.
Qed.

End Definitions.

Arguments Accepts {_}.
Arguments Language {_}.
Arguments Deterministic {_}.
Arguments Similar {_}.
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

Theorem Prod_Accepts word s t :
  Accepts A word s /\ Accepts B word t <->
  Accepts Prod word (list_prod s t).
Proof.
revert s t; induction word as [|c w]; simpl; intros.
- split.
  + intros [Ha Hb];
    apply existsb_exists in Ha as [sa Ha];
    apply existsb_exists in Hb as [sb Hb].
    apply existsb_exists; exists (sa, sb); split.
    * now apply in_prod.
    * unfold prod_accept; simpl; now b_Prop.
  + intros H.
    apply existsb_exists in H as [[sa sb] [H1 H2]].
    apply in_prod_iff in H1. unfold prod_accept in H2; simpl in H2; b_Prop.
    split; apply existsb_exists. now exists sa. now exists sb.
- split; intros.
  + eapply Accepts_subset. apply IHw, H.
    intros [sa sb] Hs. apply in_prod_iff in Hs as [Ha Hb].
    apply in_flat_map in Ha as [sa' Ha];
    apply in_flat_map in Hb as [sb' Hb].
    apply in_flat_map; exists (sa', sb'); split.
    now apply in_prod. unfold prod_trans; simpl. now apply in_prod.
  + apply IHw; eapply Accepts_subset. apply H. intros [sa sb] Hs.
    apply in_flat_map in Hs as [[sa' sb'] [H1 H2]].
    unfold prod_trans in H2; simpl in H2.
    apply in_prod_iff in H1; apply in_prod_iff in H2.
    apply in_prod; apply in_flat_map.
    now exists sa'. now exists sb'.
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

Theorem Prod_size m n :
  Finite A m -> Finite B n -> Finite Prod (m * n).
Proof.
intros [Qa [Qa_len can_a]] [Qb [Qb_len can_b]];
exists (list_prod Qa Qb); split.
simpl; now rewrite prod_length, Qa_len, Qb_len.
intros [sa sb];
destruct (can_a sa) as [sa_can Hsa];
destruct (can_b sb) as [sb_can Hsb].
exists (sa_can, sb_can); split. now apply in_prod.
intros w; simpl; rewrite ?list_prod_single.
split; intros; apply Prod_Accepts; apply Prod_Accepts in H.
all: split; [apply Hsa|apply Hsb]; easy.
Qed.

End Product_construction.

(* Automata can be made deterministic. *)
Section Powerset_construction.

Variable A : automaton letter.

Definition pow_start := [start A].
Definition pow_accept s := existsb (accept A) s.
Definition pow_trans c s := [flat_map (trans A c) s].
Definition Pow := Automaton _ _ pow_start pow_accept pow_trans.

Theorem Pow_Accepts word ss :
  Accepts Pow word ss <-> Exists (Accepts A word) ss.
Proof.
revert ss; induction word as [|c w]; simpl; intros.
- split.
  + intros H; apply existsb_exists in H as [s H].
    apply Exists_exists; now exists s.
  + intros H; apply Exists_exists in H as [s H].
    apply existsb_exists; now exists s.
- split.
  + intros H; apply IHw, Exists_exists in H as [s [H1 H2]].
    apply in_flat_map in H1 as [t [H1 H3]].
    inv H3. apply Exists_exists; now exists t.
  + intros H; apply Exists_exists in H as [s H].
    apply IHw, Exists_exists; exists (flat_map (trans A c) s); split.
    * apply in_flat_map; exists s; split. easy. apply in_eq.
    * easy.
Qed.

Corollary Pow_spec word :
  Language Pow word <-> Language A word.
Proof.
split; intros H.
- apply Pow_Accepts in H; inv H.
- apply Pow_Accepts. apply Exists_cons; now left.
Qed.

Theorem Pow_det :
  Deterministic Pow.
Proof.
easy.
Qed.

Hypothesis dec : ∀s t : state A, {s = t} + {s ≠ t}.

Theorem Pow_size n :
  Finite A n -> Finite Pow (2^n).
Proof.
intros [Q [Q_len Q_can]].
apply list_powerset with (l:=Q) in dec. 
destruct dec as [PQ [PQ_len [PQ_can _]]]; clear dec; exists PQ.
split. simpl; now rewrite PQ_len, Q_len. clear Q_len PQ_len.
(* ss_can associates ss with A-canonical states. *)
intros ss; pose(ss_can_a := map (λ s, projT1 (Q_can s)) ss).
(* ss_can associates ss_can_a with the canonical set in L. *)
destruct (PQ_can ss_can_a) as [ss_can Hss].
- intros s Hs. apply in_map_iff in Hs as [t [Hs Ht]].
  destruct (Q_can t); simpl in *; subst; easy.
- clear PQ_can. exists ss_can; split. easy.
  intros w; split; intros.
  all: apply Pow_Accepts, Exists_exists; eexists; split; [apply in_eq|].
  (* If Pow accepts w, then A accepts w from a single state s. *)
  all: apply Pow_Accepts, Exists_exists in H as [ss' [R H]]; inv R.
  all: apply Accepts_determine in H as [s [Hs H]].
  + (* Determine A-canonical state for s, and apply similarity to H. *)
    destruct (Q_can s) as [s_can Hcan] eqn:s_can_def. apply Hcan in H.
    eapply Accepts_subset. apply H. intros t Ht; inv Ht.
    apply Hss, in_map_iff; exists s. now rewrite s_can_def.
  + (* s is an A-canonical state, find an original in ss. *)
    apply Hss in Hs; apply in_map_iff in Hs as [t [R Ht]].
    destruct (Q_can t) as [t_can Hcan]; simpl in R; subst.
    apply Hcan in H. eapply Accepts_subset. apply H. intros r Hr; inv Hr.
Qed.

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

Theorem Opt_size n :
  Finite A n -> Finite Opt (S n).
Proof.
intros [Q [Q_len can]];
exists (None :: map Some Q); simpl; split.
now rewrite map_length, Q_len. intros [s|].
- destruct (can s) as [s_can Hs]; exists (Some s_can); split.
  + apply in_cons. apply in_map_iff; exists s_can; easy.
  + intros w; split; intros.
    all: apply Opt_Accepts; apply Opt_Accepts in H; simpl in *.
    all: now apply Hs.
- exists None; split. apply in_eq. easy.
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
  apply list_singleton in H as [t R]; rewrite R. apply IHw.
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

Theorem Compl_size n :
  Finite A n -> Finite Compl n.
Proof.
intros [Q [Q_len can]]; exists Q; split. easy. intros.
destruct (can s) as [s_can Hcan]; exists s_can. split. easy.
intros w; split; intros; apply Compl_Accepts; apply Compl_Accepts in H.
all: intros H'; apply H, Hcan, H'.
Qed.

End Complementation.

(* A language using a different alphabet can be decided using a projection. *)
Section Projection.

Variable A : automaton letter.
Variable new_letter : Set.
Variable proj : new_letter -> list letter.

Definition Proj_trans i s := flat_map (λ c, trans A c s) (proj i).
Definition Proj := Automaton new_letter _ (start A) (accept A) Proj_trans.

(* The image of a word in the original automaton A. *)
Definition Proj_image word image :=
  length image = length word /\ Forall2 (@In letter) image (map proj word).

Theorem Proj_Accepts word s :
  Accepts Proj word s <-> ∃image, Proj_image word image /\ Accepts A image s.
Proof.
revert s; induction word as [|c w]; simpl; intros.
- split.
  + exists nil; repeat split; simpl; easy.
  + intros [w [[H1 H2] H3]]. apply length_zero_iff_nil in H1; now subst.
- split.
  + intros. apply IHw in H as [v [[H1 H2] H3]].
    apply Accepts_determine in H3 as [t [H Ht]].
    apply in_flat_map in H as [t' [Ht' H]].
    apply in_flat_map in H as [c' Hc'].
    exists (c' :: v); repeat split; simpl.
    * now rewrite H1.
    * apply Forall2_cons; easy.
    * eapply Accepts_subset. apply Ht. intros y Hy. inv Hy; try easy.
      apply in_flat_map; exists t'; easy.
  + intros [v [[H1 H2] H3]]. destruct v; simpl in *. easy.
    inv H2. apply IHw; exists v; repeat split. lia. easy.
    eapply Accepts_subset. apply H3. intros t Ht.
    apply in_flat_map in Ht as [t' Ht].
    apply in_flat_map; exists t'; split. easy.
    apply in_flat_map; exists l; easy.
Qed.

Corollary Proj_spec word :
  Language Proj word <-> ∃image, Proj_image word image /\ Language A image.
Proof.
intros; apply Proj_Accepts.
Qed.

Theorem Proj_size n :
  Finite A n -> Finite Proj n.
Proof.
intros [Q [Q_len can]]; exists Q; split. easy. intros.
destruct (can s) as [s_can Hcan]; exists s_can; split. easy.
intros w; split; intros; apply Proj_Accepts;
apply Proj_Accepts in H as [pre H]; exists pre.
all: split; [easy|apply Hcan, H].
Qed.

End Projection.

(* For any list of states, we can find a word that is accepted by it. *)
(* The automaton must have a finite number of states. *)
Section Decidability.

(* Show that connectivity in a graph is decidable. *)
Section Connectivity.

Variable node : Type.
Variable adj : node -> list node.
Variable Terminal : node -> Prop.

Hypothesis dec : ∀v w : node, {v = w} + {v ≠ w}.
Hypothesis Terminal_dec : ∀v, {Terminal v} + {¬Terminal v}.

(* There exists a path to a terminal node in graph g. *)
Inductive Path g : node -> Prop :=
  | Path_finish v : Terminal v -> Path g v
  | Path_step v w : In w g -> In w (adj v) -> Path g w -> Path g v.

Lemma Path_subset g g' v :
  Path g' v -> (∀x, In x g' -> In x g) -> Path g v.
Proof.
intros path subset; induction path.
now apply Path_finish. eapply Path_step.
apply subset, H. all: easy.
Qed.

Lemma Path_split g g1 g2 v :
  Path g v -> (∀x, In x g <-> In x g1 \/ In x g2) ->
  Exists (Path g1) g2 \/ Path g1 v.
Proof.
intros path g_spec; induction path.
- right; now apply Path_finish.
- destruct IHpath. now left.
  apply g_spec in H as [H|H].
  + right; now apply Path_step with (w:=w).
  + left; apply Exists_exists; now exists w.
Qed.

Theorem Path_dec g v :
  {Path g v} + {¬Path g v}.
Proof.
remember (length g) as n; revert Heqn; revert g v.
apply lt_wf_rect with (n:=n); clear n; intros n IH g v g_len.
(* Check if v is a target state. *)
destruct (Terminal_dec v).
left; now apply Path_finish.
(* Determine if there is an intersection between g and adj v. *)
pose(gv := list_isect dec g (adj v)).
destruct (Nat.eq_dec (length gv) 0).
- (* No path exists since g ∩ adj v = ∅. *)
  right; intros HC; inv HC. apply in_nil with (a:=w).
  apply length_zero_iff_nil in e; rewrite <-e.
  now apply list_isect_spec.
- (* Show that g is not empty. *)
  assert(length g ≠ 0). {
    intros H; apply n1. unfold gv; rewrite list_isect_length. lia. }
  (* Determine if a node in g ∩ adj v is connected through g \ adj v. *)
  pose(g' := list_subt dec g (adj v)).
  destruct (Exists_dec (Path g') gv).
  + (* Decide using the induction hypothesis. *)
    intros; eapply IH. 2: reflexivity.
    unfold g'; rewrite g_len, list_subt_length.
    fold gv; lia.
  + (* A path exists. *)
    left. apply Exists_exists in e as [w [H1w H2w]].
    apply list_isect_spec in H1w.
    apply Path_step with (w:=w); try easy.
    eapply Path_subset. apply H2w.
    intros; eapply list_subt_spec, H0.
  + (* Any path would yield a contradiction. *)
    right. intros Hv; apply n2.
    apply Path_split with (g1:=g')(g2:=gv) in Hv as [Hv|Hv].
    (* Either we find a path through g', or we find an impossible path. *)
    easy. exfalso; inv Hv. apply list_subt_spec in H0; easy.
    (* Show that g = g1 ∪ g2. *)
    intros w; split; intros.
    * destruct (in_dec dec w (adj v)).
      right; now apply list_isect_spec.
      left; now apply list_subt_spec.
    * destruct H0.
      now apply list_subt_spec in H0.
      now apply list_isect_spec in H0.
Qed.

End Connectivity.

Arguments Path {_}.

Variable alphabet : list letter.
Hypothesis full_alphabet : ∀c, In c alphabet.

Variable A : automaton letter.
Hypothesis state_dec : ∀s t : state A, {s = t} + {s ≠ t}.

(* Reduce finding an accepting word to connectivity to an accept state. *)
Section Accepting_path.
 
Variable Q : list (state A).
Variable can : state A -> state A.
Hypothesis can_spec : ∀s, In (can s) Q /\ Similar A [s] [can s].

Definition Automaton_adj s := map can (flat_map (λ c, trans A c s) alphabet).
Definition Accepting_path := Path Automaton_adj (λ s, accept A s = true) Q.

Theorem Accepting_path_Accepts s :
  Accepting_path s -> ∃w, Accepts A w [s].
Proof.
intros path; induction path.
- exists nil; simpl; now rewrite H.
- apply in_map_iff in H0 as [s [R Hs]]; subst.
  apply in_flat_map in Hs as [c [_ Hc]].
  destruct IHpath as [w Hw].
  exists (c :: w); simpl; rewrite app_nil_r.
  eapply Accepts_subset. apply can_spec, Hw.
  intros s' Hs'; inv Hs'.
Qed.

Theorem Accepts_Accepting_path s w :
  Accepts A w [s] -> Accepting_path s.
Proof.
revert s; induction w as [|c w]; simpl; intros.
- rewrite orb_false_r in H. now apply Path_finish.
- rewrite app_nil_r in H.
  apply Accepts_determine in H as [t [Ht Hw]].
  apply can_spec, IHw in Hw.
  apply Path_step with (w:=can t). apply can_spec.
  apply in_map_iff; exists t; split. easy.
  apply in_flat_map; exists c; easy. easy.
Qed.

Corollary Accepting_path_dec s :
  {Accepting_path s} + {¬Accepting_path s}.
Proof.
apply Path_dec. apply state_dec.
intros v; destruct (accept A v); auto.
Qed.

End Accepting_path.

Variable size : nat.
Hypothesis A_size : Finite A size.

Corollary ex_Accepts_dec s :
  {∃w, Accepts A w [s]} + {∀w, ¬Accepts A w [s]}.
Proof.
destruct A_size as [Q [Q_len can]].
pose(can_f s := projT1 (can s)).
assert(can_f_spec : ∀t, In (can_f t) Q /\ Similar A [t] [can_f t]). {
  intros; unfold can_f; destruct (can t); easy. }
destruct (Accepting_path_dec Q can_f s).
- left. eapply Accepting_path_Accepts.
  apply can_f_spec. easy.
- right; intros w. eapply contra.
  apply Accepts_Accepting_path, can_f_spec. easy.
Qed.

Corollary Language_inhabited_dec :
  {∃w, Language A w} + {∀w, ¬Language A w}.
Proof.
apply ex_Accepts_dec.
Qed.

End Decidability.

End Results.
