(* Basic theory of automata. *)

Require Import Utf8 Bool PeanoNat List Lia.
From larith Require Import tactics notations utilities path.
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

(* A state automorphism. *)
Definition Automorphism f := ∀s, accept A s = accept A (f s) /\
  ∀c t, In (f t) (map f (trans A c s)) <-> In (f t) (map f (trans A c (f s))).

(* A finite automaton has an automorphism with a finite domain. *)
Notation Range f r := (∀x, In (f x) r).
Definition Finite n := Σ f Q, length Q = n /\ Range f Q /\ Automorphism f.

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
  Accepts w s <-> ∃t, In t s /\ Accepts w [t].
Proof.
induction s; simpl; intros.
- split; intros; exfalso.
  eapply not_Accepts_nil, H. now destruct H.
- replace (a :: s) with ([a] ++ s) by easy.
  rewrite Accepts_app, IHs. split.
  + intros [H|[t H]]; [exists a|exists t]; split.
    now left. easy. now right. easy.
  + intros [t [[R|Hs] Ht]]; subst. now left.
    right; exists t; easy.
Qed.

Theorem Aut_Accepts f s w :
  Automorphism f -> Accepts w [s] <-> Accepts w [f s].
Proof.
intros aut; revert s; induction w as [|c w]; simpl; intros.
- rewrite ?orb_false_r. apply eq_iff_eq_true, aut.
- rewrite ?app_nil_r, ?Accepts_determine.
  split; intros [t [Hs Ht]].
  all: apply in_map with (f:=f), aut, in_map_iff in Hs as [t' [R Ht']].
  all: apply IHw in Ht; rewrite <-R in Ht; apply IHw in Ht.
  all: exists t'; easy.
Qed.

End Definitions.

Arguments Accepts {_}.
Arguments Language {_}.
Arguments Deterministic {_}.
Arguments Automorphism {_}.
Arguments Finite {_}.

Module Automata.

Section Constructions.

Variable letter : Set.

(* Track two automata at once to decide the complement of two languages. *)
Section Product.

Variable A B : automaton letter.

Definition prod_start := (start A, start B).
Definition prod_accept s := accept A (fst s) && accept B (snd s).
Definition prod_trans c s := list_prod (trans A c (fst s)) (trans B c (snd s)).
Definition prod := Automaton _ _ prod_start prod_accept prod_trans.

Theorem prod_Accepts word s t :
  Accepts A word s /\ Accepts B word t <->
  Accepts prod word (list_prod s t).
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

Corollary prod_spec word :
  Language prod word <-> Language A word /\ Language B word. 
Proof.
symmetry; apply prod_Accepts.
Qed.

Theorem prod_det :
  Deterministic A -> Deterministic B -> Deterministic prod.
Proof.
intros H1 H2 c [x y].
simpl; unfold prod_trans; simpl.
now rewrite prod_length, H1, H2.
Qed.

Theorem prod_size m n :
  Finite A m -> Finite B n -> Finite prod (m * n).
Proof.
intros [f [Q [Q_len [f_ran f_aut]]]];
intros [g [R [R_len [g_ran g_aut]]]].
exists (λ s, (f (fst s), g (snd s))), (list_prod Q R); split; [|split].
- simpl; rewrite prod_length, Q_len, R_len; easy.
- intros [s t]; simpl; apply in_prod; easy.
- (* The mapping is an automorphism. *)
  intros [s t]; simpl; split.
  + unfold prod_accept; simpl.
    rewrite (proj1 (f_aut s)), (proj1 (g_aut t)); reflexivity.
  + intros c [s' t']; unfold prod_trans; simpl.
    rewrite ?in_map_iff; split; intros [[s'' t''] [H1 H2]]; simpl in *.
    all: inv H1; apply in_prod_iff in H2 as [Hs Ht].
    all: apply in_map with (f:=f), f_aut, in_map_iff in Hs as [s''' [eq_s Hs]].
    all: apply in_map with (f:=g), g_aut, in_map_iff in Ht as [t''' [eq_t Ht]].
    all: exists (s''', t'''); simpl; split; [congruence|].
    all: apply in_prod; easy.
Qed.

End Product.

(* Make a deteministic automaton by tracking all reachable states. *)
Section Powerset.

Variable A : automaton letter.

Definition pow_start := [start A].
Definition pow_accept s := existsb (accept A) s.
Definition pow_trans c s := [flat_map (trans A c) s].
Definition pow := Automaton _ _ pow_start pow_accept pow_trans.

Theorem pow_Accepts word ss :
  Accepts pow word ss <-> Exists (Accepts A word) ss.
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

Corollary pow_spec word :
  Language pow word <-> Language A word.
Proof.
split; intros H.
- apply pow_Accepts in H; inv H.
- apply pow_Accepts. apply Exists_cons; now left.
Qed.

Theorem pow_det :
  Deterministic pow.
Proof.
easy.
Qed.

Hypothesis dec : ∀s t : state A, {s = t} + {s ≠ t}.

Theorem pow_size n :
  Finite A n -> Finite pow (2^n).
Proof.
intros [f [Q [Q_len [f_ran f_aut]]]].
pose(g s := powerset_lookup dec Q (map f s)).
exists g, (powerset Q); split; [|split].
- rewrite <-Q_len; apply powerset_length.
- intros; apply powerset_lookup_in.
- (* g is an automorphism. *)
  intros s; simpl.
  assert(Hh : ∀x, In x (map f s) <-> In x (g s)). {
    apply powerset_lookup_eqv; intros y H.
    apply in_map_iff in H as [x [H _]]; subst.
    apply f_ran. }
  split.
  + (* Same accept states. *)
    unfold pow_accept; apply eq_iff_eq_true.
    rewrite ?existsb_exists; split; intros [t [H1 H2]].
    * exists (f t); split. rewrite <-Hh; apply in_map, H1.
      rewrite <-(proj1 (f_aut t)); apply H2.
    * apply Hh, in_map_iff in H1 as [t' [eq H1]]; subst.
      exists t'; split. easy. rewrite (proj1 (f_aut t')); apply H2.
  + (* Same transitions. *)
    intros. rewrite ?or_remove_r with (Q:=False); try easy.
    apply eq_iff, powerset_lookup_wd; intros.
Admitted.

End Powerset.

(* Add a default rejection state None. *)
Section Option.

Variable A : automaton letter.

Definition opt_accept s :=
  match s with
  | None => false
  | Some s' => accept A s'
  end.

Definition opt_trans c s :=
  match s with
  | None => [None]
  | Some s' =>
    let t := trans A c s' in
    if length t =? 0
    then [None]
    else map Some t
  end.

Definition opt := Automaton _ _ (Some (start A)) opt_accept opt_trans.

Theorem opt_Accepts word s :
  Accepts opt word s <-> Accepts A word (strip s).
Proof.
revert s; induction word as [|c w]; simpl; intros.
- (* To avoid needing decidability over (state A), we use induction again. *)
  induction s as [|[a|] s]; simpl. easy. 2: apply IHs.
  split; intros; b_Prop.
  1,3: now left. 1,2: right; now apply IHs.
- replace (flat_map (trans A c) (strip s))
  with (strip (flat_map (opt_trans c) s)). apply IHw.
  induction s as [|[a|] s]; simpl. easy. 2: apply IHs.
  remember (trans A c a) as t; destruct t; simpl. apply IHs.
  now rewrite strip_app, strip_map_id, IHs.
Qed.

Corollary opt_spec word :
  Language opt word <-> Language A word.
Proof.
intros; apply opt_Accepts.
Qed.

Theorem opt_det :
  (∀c s, length (trans A c s) <= 1) -> Deterministic opt.
Proof.
intros H c [s|]; simpl. 2: easy.
destruct (length (trans A c s) =? 0) eqn:E; simpl; b_Prop.
easy. assert(Hcs := H c s). rewrite map_length; lia.
Qed.

Theorem opt_size n :
  Finite A n -> Finite opt (S n).
Proof.
Admitted.

End Option.

(* Accept the complement of a language by inverting the accept states. *)
Section Complementation.

Variable A : automaton letter.
Hypothesis det : Deterministic A.

Definition compl := Automaton _ _
  (start A) (λ s, negb (accept A s)) (trans A).

Theorem compl_Accepts word s :
  Accepts compl word [s] <-> ¬Accepts A word [s].
Proof.
revert s; induction word as [|c w]; simpl; intros.
- now destruct (accept A s).
- rewrite app_nil_r. assert(H := det c s).
  apply list_singleton in H as [t R]; rewrite R. apply IHw.
Qed.

Corollary compl_spec word :
  Language compl word <-> ¬Language A word.
Proof.
intros; apply compl_Accepts.
Qed.

Theorem compl_det :
  Deterministic compl.
Proof.
easy.
Qed.

Theorem compl_size n :
  Finite A n -> Finite compl n.
Proof.
Admitted.

End Complementation.

(* Change the alphabet using a projection function. *)
Section Projection.

Variable A : automaton letter.
Variable new_letter : Set.
Variable pr : new_letter -> list letter.

Definition proj_trans i s := flat_map (λ c, trans A c s) (pr i).
Definition proj := Automaton new_letter _ (start A) (accept A) proj_trans.

(* The image of a word in the original automaton A. *)
Definition Image word image := Forall2 (@In letter) image (map pr word).

Theorem proj_Accepts word s :
  Accepts proj word s <-> ∃v, Image word v /\ Accepts A v s.
Proof.
revert s; induction word as [|c w]; simpl; intros.
- split.
  + exists nil; split. apply Forall2_nil. easy.
  + intros [w [H1 H2]]; inv H1.
- split.
  + intros. apply IHw in H as [v [H1 H2]].
    apply Accepts_determine in H2 as [t [H Ht]].
    apply in_flat_map in H as [t' [Ht' H]].
    apply in_flat_map in H as [c' Hc'].
    exists (c' :: v); simpl; split.
    * now apply Forall2_cons.
    * eapply Accepts_subset. apply Ht. intros y Hy. inv Hy; try easy.
      apply in_flat_map; exists t'; easy.
  + intros [v [H1 H2]]. destruct v; simpl in *. easy.
    inv H1. apply IHw; exists v; repeat split. easy.
    eapply Accepts_subset. apply H2. intros t Ht.
    apply in_flat_map in Ht as [t' Ht].
    apply in_flat_map; exists t'; split. easy.
    apply in_flat_map; exists l; easy.
Qed.

Corollary proj_spec word :
  Language proj word <-> ∃v, Image word v /\ Language A v.
Proof.
intros; apply proj_Accepts.
Qed.

Theorem proj_det :
  Deterministic A -> (∀c, length (pr c) = 1) -> Deterministic proj.
Proof.
intros det Hc c s. simpl; unfold proj_trans.
destruct (list_singleton _ (Hc c));
rewrite H; simpl; rewrite app_nil_r. apply det.
Qed.

Theorem proj_size n :
  Finite A n -> Finite proj n.
Proof.
Admitted.

End Projection.

(* Remove a suffix of padding-symbols using 'early accept' states. *)
Section Retraction.

Variable A : automaton letter.
Variable p : letter.

Fixpoint retr_accept n s : bool :=
  match n with
  | 0 => false
  | S m => accept A s || existsb (retr_accept m) (trans A p s)
  end.

(* Define early accept states using graph connectivity. *)
Section Early_accept_states.

Variable Q : list (state A).
Variable aut : state A -> state A.
Hypothesis aut_ran : ∀s, In (aut s) Q.
Hypothesis aut_spec : Automorphism A aut.

Definition suffix_adj s := map aut (trans A p s).
Definition Early_accept := Connected suffix_adj (λ s, accept A s = true) Q.
Notation suffix_path := (path suffix_adj (λ s, accept A s = true) Q).

Theorem Early_accept_complete s n :
  Accepts A (repeat p n) [s] -> Early_accept s.
Proof.
revert s; induction n; simpl; intros.
- rewrite orb_false_r in H; apply conn, path_stop, H.
- rewrite app_nil_r in H; apply Accepts_determine in H as [t [Hs Ht]].
  apply Aut_Accepts with (f:=aut), IHn in Ht as [path].
  apply conn, path_step with (w:=aut t).
  apply aut_ran. apply in_map, Hs. apply path. apply aut_spec.
Qed.

Theorem retr_accept_sound n s :
  retr_accept n s = true -> ∃n, Accepts A (repeat p n) [s].
Proof.
revert s; induction n; simpl; intros. easy. b_Prop.
- exists 0; simpl. rewrite e; easy.
- apply existsb_exists in e as [t [Hs Ht]].
  apply IHn in Ht as [m Ht]; exists (S m); simpl.
  rewrite app_nil_r; apply Accepts_determine; exists t; easy.
Qed.

Theorem retr_accept_complete s (path : suffix_path s) :
  retr_accept (1 + path_length path) s = true.
Proof.
induction path; simpl; b_Prop.
now left. right; apply existsb_exists.
apply in_map_iff in i0 as [t [R H]]; subst; exists t; split. easy.
simpl in IHpath; b_Prop; [left|right].
Admitted.

Lemma retr_accept_weaken m n s :
  retr_accept m s = true -> m <= n -> retr_accept n s = true.
Proof.
revert n s; induction m; simpl; intros.
easy. destruct n; simpl. easy. b_Prop. now left. right.
apply existsb_exists in e as [t H]; apply existsb_exists; exists t.
split. easy. apply IHm. easy. lia.
Qed.

Theorem retr_accept_spec s :
  existsb (retr_accept (1 + length Q)) s = true <->
  ∃n, Accepts A (repeat p n) s.
Proof.
rewrite existsb_exists; split; intros [i H].
- destruct H as [Hs Hi]. apply retr_accept_sound in Hi as [n Hn]; exists n.
  apply Accepts_determine; exists i; easy.
- apply Accepts_determine in H as [t [Hs Ht]]; exists t; split. easy.
  apply Early_accept_complete in Ht as [path].
  apply short_path in path as [spath H].
  eapply retr_accept_weaken. apply retr_accept_complete. apply le_n_S, H.
Admitted.

End Early_accept_states.

Variable size : nat.
Hypothesis finite : Finite A size.

Definition retr := Automaton _ _ (start A) (retr_accept (S size)) (trans A).

Theorem retr_Accepts word s :
  Accepts retr word s <-> ∃n, Accepts A (word ++ repeat p n) s.
Proof.
revert s; induction word as [|c w]; simpl; intros.
- destruct finite as [f [Q [Q_len [f_ran f_spec]]]].
  rewrite <-Q_len; apply retr_accept_spec with (aut:=f); easy.
- apply IHw.
Qed.

Corollary retr_spec word :
  Language retr word <-> ∃n, Language A (word ++ repeat p n).
Proof.
apply retr_Accepts.
Qed.

Theorem retr_det :
  Deterministic A -> Deterministic retr.
Proof.
easy.
Qed.

Theorem retr_size :
  Finite retr size.
Proof.
Admitted.

End Retraction.

End Constructions.

End Automata.

(* For any list of states, we can find a word that is accepted by it. *)
(* The automaton must have a finite number of states. *)
Section Decidability.

Variable letter : Set.
Variable alphabet : list letter.
Hypothesis full_alphabet : ∀c, In c alphabet.

Variable A : automaton letter.
Hypothesis state_dec : ∀s t : state A, {s = t} + {s ≠ t}.

(* Reduce finding an accepting word to connectivity to an accept state. *)
Section Connectivity_to_an_accept_state.

Variable Q : list (state A).
Variable aut : state A -> state A.
Hypothesis aut_ran : ∀s, In (aut s) Q.
Hypothesis aut_spec : Automorphism A aut.

Definition trans_adj s := map aut (flat_map (λ c, trans A c s) alphabet).
Definition Acceptable := Connected trans_adj (λ s, accept A s = true) Q.

Theorem Acceptable_Accepts s :
  Acceptable s -> ∃w, Accepts A w [s].
Proof.
intros [p]; induction p.
- exists nil; simpl; now rewrite e.
- apply in_map_iff in i0 as [s [R Hs]]; subst.
  apply in_flat_map in Hs as [c [_ Hc]].
  destruct IHp as [w Hw]; exists (c :: w); simpl.
  rewrite app_nil_r; eapply Accepts_subset.
  apply Aut_Accepts with (f:=aut), Hw; easy.
  intros s' Hs'; inv Hs'.
Qed.

Theorem Accepts_Acceptable s w :
  Accepts A w [s] -> Acceptable s.
Proof.
revert s; induction w as [|c w]; simpl; intros.
- rewrite orb_false_r in H. now apply conn, path_stop.
- rewrite app_nil_r in H.
  apply Accepts_determine in H as [t [Ht Hw]].
  apply Aut_Accepts with (f:=aut), IHw in Hw as [p].
  apply conn, path_step with (w:=aut t). apply aut_ran.
  apply in_map_iff; exists t; split. easy.
  apply in_flat_map; exists c; easy. easy.
  apply aut_spec.
Qed.

Corollary Acceptable_dec s :
  {Acceptable s} + {¬Acceptable s}.
Proof.
apply Connected_dec. apply state_dec.
intros v; destruct (accept A v); auto.
Qed.

End Connectivity_to_an_accept_state.

Variable size : nat.
Hypothesis finite : Finite A size.

Corollary ex_Accepts_dec s :
  {∃w, Accepts A w [s]} + {∀w, ¬Accepts A w [s]}.
Proof.
destruct finite as [f [Q [Q_len [f_ran f_aut]]]].
destruct (Acceptable_dec Q f s).
- left; eapply Acceptable_Accepts. apply f_aut. apply a.
- right; intros w; eapply contra. apply Accepts_Acceptable.
  apply f_ran. apply f_aut. easy.
Qed.

Corollary Language_inhabited_dec :
  {∃w, Language A w} + {∀w, ¬Language A w}.
Proof.
apply ex_Accepts_dec.
Qed.

End Decidability.
