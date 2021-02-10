(* Basic theory of automata. *)

Require Import Utf8 Bool PeanoNat List Eqdep_dec.
From larith Require Import tactics notations utilities dfs.
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

(* A word is in the language if it is accepted from the start state. *)
Definition Language word := Accepts word [start A].

(* An automaton is deterministic if every transition has 1 target state. *)
Definition Deterministic := ∀c s, length (trans A c s) = 1.

(* There are finitely many states if they all fit on a list. *)
Definition Finite n := Σ Q, length Q = n /\ ∀s : state A, In s Q.

Theorem not_Accepts_nil w :
  ¬Accepts w [].
Proof.
now induction w.
Qed.

Theorem Accepts_incl w s1 s2 :
  (∀s, In s s1 -> In s s2) -> Accepts w s1 -> Accepts w s2.
Proof.
revert s1 s2; induction w; simpl; intros s1 s2 H.
- rewrite ?existsb_exists; intros [x Hx]; exists x.
  split. apply H, Hx. apply Hx.
- apply IHw; intros s; rewrite ?in_flat_map.
  intros [x Hx]; exists x; split. apply H, Hx. apply Hx.
Qed.

Corollary Accepts_eqv w s1 s2 :
  (∀s, In s s1 <-> In s s2) -> Accepts w s1 <-> Accepts w s2.
Proof.
intros; split; apply Accepts_incl, H.
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
  + intros [t [[eq_t|Hs] Ht]]; subst. now left.
    right; exists t; easy.
Qed.

End Definitions.

Arguments Accepts {_}.
Arguments Language {_}.
Arguments Deterministic {_}.
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
- rewrite ?existsb_exists; split.
  + intros [[sa Ha] [sb Hb]]; exists (sa, sb); split.
    now apply in_prod. unfold prod_accept; simpl; b_Prop; easy.
  + intros [[sa sb] [H1 H2]]; apply in_prod_iff in H1.
    unfold prod_accept in H2; simpl in H2; b_Prop.
    split; [exists sa|exists sb]; easy.
- rewrite IHw; apply Accepts_eqv; intros [sa sb].
  simpl; rewrite in_prod_iff, ?in_flat_map; split.
  + intros [[sa' Ha] [sb' Hb]]; exists (sa', sb').
    split; apply in_prod; easy.
  + intros [[sa' sb'] [Ha Hb]].
    apply in_prod_iff in Ha; apply in_prod_iff in Hb; simpl in *.
    split; [exists sa'|exists sb']; easy.
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
intros [Q [Q_len Q_spec]] [R [R_len R_spec]].
exists (list_prod Q R); split.
- simpl; rewrite prod_length, Q_len, R_len; reflexivity.
- intros [sa sb]; apply in_prod; easy.
Defined.

End Product.

(* Make a deteministic automaton by tracking all reachable states. *)
Section Powerset.

Variable A : automaton letter.
Variable Q : list (state A).
Hypothesis Q_spec : ∀s, In s Q.
Hypothesis dec : ∀s t : state A, {s = t} + {s ≠ t}.

Notation pow_state := (Σ ns, normalize dec Q ns = ns).
Definition pow_norm s : pow_state :=
  existT _ (normalize _ _ s) (normalize_normalize _ _ _ s).

Definition pow_start := pow_norm [start A].
Definition pow_accept (s : pow_state) := existsb (accept A) (projT1 s).
Definition pow_trans c (s : pow_state) :=
  [pow_norm (flat_map (trans A c) (projT1 s))].

Definition pow := Automaton _ _ pow_start pow_accept pow_trans.

Theorem pow_Accepts word ss :
  Accepts pow word (map pow_norm ss) <-> Exists (Accepts A word) ss.
Proof.
revert ss; induction word as [|c w]; simpl; intros.
- (* Valid accept states. *)
  rewrite existsb_exists, Exists_exists; split.
  + (* pow accepts -> A accepts *)
    intros [[s s_norm] []].
    unfold pow_accept in H0; simpl in H0.
    apply in_map_iff in H as [s' []]; inv H.
    exists s'; split. easy.
    apply existsb_exists in H0 as [s'' []].
    rewrite existsb_exists; exists s''; split.
    eapply normalize_sound, H. easy.
  + (* A accepts -> pow accepts. *)
    intros [s []]; exists (pow_norm s); split. apply in_map, H.
    apply existsb_exists in H0 as [s' []].
    apply existsb_exists; exists s'; split.
    apply normalize_complete. all: easy.
- (* Valid transitions. *)
  unfold pow_trans.
  rewrite flat_map_singleton, map_map, <-map_map.
  rewrite IHw, ?Exists_exists; split; intros [s []].
  + apply in_map_iff in H as [s' []]; subst.
    exists s'; split. easy. eapply Accepts_incl. 2: apply H0.
    intros s; rewrite ?in_flat_map; intros [s'' []].
    exists s''; split. eapply normalize_sound, H. easy.
  + eexists; split. apply in_map_iff; eexists; split.
    reflexivity. apply H. eapply Accepts_incl. 2: apply H0.
    intros s'; rewrite ?in_flat_map; intros [s'' []].
    exists s''; split. apply normalize_complete. all: easy.
Qed.

Theorem pow_spec word :
  Language pow word <-> Language A word.
Proof.
unfold Language; simpl; unfold pow_start.
replace ([pow_norm _]) with (map pow_norm [[start A]]) by easy.
rewrite pow_Accepts, Exists_cons, Exists_nil, or_remove_r; easy.
Qed.

Theorem pow_det :
  Deterministic pow.
Proof.
easy.
Qed.

(* I do not know what magic makes this work, but I am happy it does! *)
Lemma pow_state_eq (s s' : pow_state) :
  projT1 s = projT1 s' -> s = s'.
Proof.
destruct s, s'; simpl; intros; subst. replace e with e0. easy.
apply eq_proofs_unicity_on.
intros; edestruct list_eq_dec. apply dec.
left; apply e1. now right.
Qed.

Theorem pow_size :
  Finite pow (2^length Q).
Proof.
exists (map pow_norm (powerset Q)); split.
- rewrite map_length; apply powerset_length.
- intros [s H]; apply in_map_iff; exists s; split.
  + apply pow_state_eq; apply H.
  + rewrite <-H; apply normalize_spec.
Defined.

Theorem pow_dec (s t : pow_state) :
  {s = t} + {s ≠ t}.
Proof.
edestruct list_eq_dec. apply dec.
- left; apply pow_state_eq, e.
- right; intros H; subst; easy.
Defined.

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
easy. assert(Hcs := H c s). rewrite map_length.
apply Nat.le_1_r in Hcs as []; easy.
Qed.

Theorem opt_size n :
  Finite A n -> Finite opt (S n).
Proof.
intros [Q [Q_len Q_spec]]; exists (None :: map Some Q); split.
- simpl; rewrite map_length, Q_len; reflexivity.
- intros [s|]. apply in_cons, in_map, Q_spec. apply in_eq.
Defined.

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
- rewrite IHw; split; intros [v [H1 H2]].
  + apply Accepts_determine in H2 as [t [H Ht]].
    apply in_flat_map in H as [t' [Ht' H]].
    apply in_flat_map in H as [c' Hc'].
    exists (c' :: v); simpl; split.
    * now apply Forall2_cons.
    * eapply Accepts_incl. 2: apply Ht.
      intros t'' Ht''; inv Ht''.
      apply in_flat_map; exists t'; easy.
  + destruct v; simpl in *. easy. inv H1.
    exists v; repeat split. easy.
    eapply Accepts_incl. 2: apply H2.
    intros t; rewrite ?in_flat_map.
    intros [t' Ht]; exists t'; split.
    easy. apply in_flat_map; exists l; easy.
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

End Projection.

(* Remove a suffix of padding-symbols using 'early accept' states. *)
Section Saturation.

Variable A : automaton letter.
Variable p : letter.
Variable size : nat.
Hypothesis finite : Finite A size.
Hypothesis dec : ∀s t : state A, {s = t} + {s ≠ t}.

Notation solve := (dfs (trans A p) (accept A) dec size []).
Notation Solution := (DFS_solution (trans A p) (accept A) dec []).

Definition sat_accept s :=
  match solve s with
  | inl _ => false
  | inr _ => true
  end.

Definition sat := Automaton _ _ (start A) sat_accept (trans A).

Lemma sat_Solution_Accepts path s :
  Solution s path -> Accepts A (repeat p (length path)) [s].
Proof.
revert s; induction path; simpl; intros; destruct H as [[]].
- simpl in H1; rewrite H1; easy.
- rewrite app_nil_r; inv H. apply in_remove in H6 as [H6 _].
  apply Accepts_determine; exists a; split; [easy|].
  apply IHpath; repeat split. easy. inv H0.
  rewrite last_cons in H1; easy.
Qed.

Lemma Accepts_sat_Solution n s :
  Accepts A (repeat p n) [s] -> ∃path, Solution s path.
Proof.
revert s; induction n; simpl; intros.
- rewrite orb_false_r in H; exists []; apply DFS_solution_refl; easy.
- rewrite app_nil_r in H; apply Accepts_determine in H as [t []].
  apply IHn in H0 as [path H0]. destruct (dec t s); subst.
  exists path; apply H0. exists (t :: path).
  apply DFS_solution_cons; [apply H0|apply in_in_remove; easy].
Qed.

Theorem sat_solve_sound s path :
  solve s = inr path -> Accepts A (repeat p (length path)) [s].
Proof.
intros; apply dfs_sound in H.
apply sat_Solution_Accepts, H.
Qed.

Theorem sat_solve_complete n s :
  Accepts A (repeat p n) [s] -> ∃path, solve s = inr path.
Proof.
intros; apply Accepts_sat_Solution in H as [path H].
destruct finite as [Q [Q_len Q_spec]].
apply dfs_complete with (graph:=Q)(path:=path). apply Q_spec.
rewrite subtract_length, Q_len; apply Nat.le_sub_l. apply H.
Qed.

Theorem sat_Accepts word s :
  Accepts sat word s <-> ∃n, Accepts A (word ++ repeat p n) s.
Proof.
revert s; induction word as [|c w]; simpl; intros.
- unfold sat_accept; rewrite existsb_exists; split.
  + intros [t []].
    destruct (solve _) eqn:Ht; [easy|].
    exists (length l); apply Accepts_determine.
    exists t; split; [easy|apply sat_solve_sound, Ht].
  + intros [n Hn];
    apply Accepts_determine in Hn as [t []]. exists t; split; [easy|].
    apply sat_solve_complete in H0 as [path H0].
    rewrite H0; reflexivity.
- apply IHw.
Qed.

Corollary sat_spec word :
  Language sat word <-> ∃n, Language A (word ++ repeat p n).
Proof.
apply sat_Accepts.
Qed.

End Saturation.

End Constructions.

End Automata.

Arguments Automata.Image {_ _}.

(* For any list of states, we can find a word that is accepted by it. *)
(* The automaton must have a finite number of states. *)
Section Decidability.

Variable letter : Set.
Variable alphabet : list letter.
Hypothesis full_alphabet : ∀c, In c alphabet.

Variable A : automaton letter.
Hypothesis dec : ∀s t : state A, {s = t} + {s ≠ t}.

Definition trans_adj s := nodup dec (flat_map (λ c, trans A c s) alphabet).
Definition Accepting := DFS_solution trans_adj (accept A) dec [].

Theorem Accepting_Accepts s path :
  Accepting s path -> Σ w, Accepts A w [s].
Proof.
Admitted.

Theorem Accepts_Accepting s w :
  Accepts A w [s] -> ∃path, Accepting s path.
Proof.
Admitted.

Variable size : nat.
Hypothesis finite : Finite A size.

Theorem Accepts_inhabited_dec s :
  (Σ w, Accepts A w [s]) + {∀w, ¬Accepts A w [s]}.
Proof.
assert(fin : ∃Q, length Q = size /\ ∀t : state A, In t Q).
destruct finite as [Q HQ]; exists Q; apply HQ.
destruct (depth_first_search _ trans_adj (accept A) dec size fin [] s).
- destruct s0 as [path H]; left; eapply Accepting_Accepts. apply H.
- right; intros w Hw. apply Accepts_Accepting in Hw as [path H].
  apply n with (path:=path), H.
Defined.

Corollary Language_inhabited_dec :
  (Σ w, Language A w) + {∀w, ¬Language A w}.
Proof.
apply Accepts_inhabited_dec.
Defined.

End Decidability.
