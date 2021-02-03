(* Theorems about connections in finite graphs. *)

Require Import Utf8 PeanoNat Wf_nat List Lia.
From larith Require Import tactics notations utilities.
Import ListNotations.

Section Connecting_paths.

Variable node : Type.
Variable adj : node -> list node.
Variable End : node -> Prop.

Hypothesis dec : ∀v w : node, {v = w} + {v ≠ w}.
Hypothesis End_dec : ∀v, {End v} + {¬End v}.

(* A path to an end node in graph g. *)
Inductive path G : node -> Type :=
  | path_stop v : End v -> path G v
  | path_step v w : In w G -> In w (adj v) -> path G w -> path G v.

Inductive Connected G v : Prop :=
  | conn : path G v -> Connected G v.

Fixpoint path_length {G n} (p : path G n) : nat :=
  match p with
  | path_stop _ _ _ => 0
  | path_step _ _ _ _ _ q => S (path_length q)
  end.

(* If G ⊆ H, then a path through G is a path through H. *)
Theorem path_subset G H v (p : path G v) :
  (∀x, In x G -> In x H) -> Σ q : path H v, path_length q = path_length p.
Proof.
intros subset; induction p.
- exists (path_stop _ v e); easy.
- destruct IHp as [q IH].
  exists (path_step _ v w (subset w i) i0 q).
  simpl; rewrite IH; reflexivity.
Qed.

(* If G ⊆ Ga ∪ Gb, then a path through G can be split up between Ga and Gb. *)
Theorem path_split G Ga Gb v :
  path G v -> (∀x, In x G -> {In x Ga} + {In x Gb}) ->
  path Ga v + Σ w, In w Gb × path Ga w.
Proof.
intros p g_spec; induction p.
- left; apply path_stop, e.
- destruct IHp.
  apply g_spec in i as [H1|H2].
  + left; now apply path_step with (w:=w).
  + right; exists w; easy.
  + right; easy.
Qed.

(* We can effectively determine if v is connected to an end node. *)
Theorem Connected_dec G v :
  {Connected G v} + {¬Connected G v}.
Proof.
remember (length G) as n; apply eq_sym in Heqn; revert Heqn; revert G v.
apply lt_wf_rect with (n:=n); clear n; intros n IH G v G_size.
(* Check if v is a target state. *)
destruct (End_dec v).
left; apply conn, path_stop, e.
(* Determine if there is an intersection between G and adj v. *)
pose(Gv := intersect dec G (adj v)).
destruct (Nat.eq_dec (length Gv) 0).
- (* No path exists since G ∩ adj v = ∅. *)
  right; intros [p]; inv p. apply in_nil with (a:=w).
  apply length_zero_iff_nil in e; rewrite <-e.
  now apply intersect_spec.
- (* Show that G is not empty. *)
  assert(length G ≠ 0). {
    intros H; apply n1. unfold Gv; rewrite intersect_length. lia. }
  (* Determine if a node in G ∩ adj v is connected through G \ adj v. *)
  pose(G' := subtract dec G (adj v)).
  destruct (Exists_dec (Connected G') Gv).
  + (* Decide using the induction hypothesis. *)
    intros; eapply IH. 2: reflexivity.
    unfold G'; rewrite <-G_size, subtract_length.
    fold Gv; lia.
  + (* A path exists. *)
    left. apply Exists_exists in e as [w [H1w [p]]].
    apply intersect_spec in H1w.
    apply conn, path_step with (w:=w); try easy.
    eapply path_subset. apply p.
    intros; eapply subtract_spec, H0.
  + (* Any path would yield a contradiction. *)
    right. intros [p]; apply n2.
    apply path_split with (Ga:=G')(Gb:=Gv) in p as [p|[w []]].
    (* A path through G' yields a contradiction. *)
    * inv p; apply subtract_spec in H0; easy.
    * apply Exists_exists; exists w; easy.
    * intros w Hw; destruct (in_dec dec w (adj v)).
      right; now apply intersect_spec.
      left; now apply subtract_spec.
Qed.

Theorem path_pop G v :
  path G v -> path (remove dec v G) v.
Proof.
intros p; apply path_split with (Ga:=remove dec v G)(Gb:=[v]) in p.
destruct p as [p|[w [Hw p]]]. apply p. apply in_inv in Hw.
simpl in Hw; rewrite or_remove_r in Hw; subst. apply p. easy.
intros; destruct (dec x v).
- right; subst; apply in_eq.
- left; apply in_in_remove; easy.
Qed.

(* A path can be shortened to at most the size of the graph (PHP). *)
Theorem short_path G v (p : path G v) :
  Σ q : path G v, path_length q <= length G.
Proof.
remember (length G) as n; apply eq_sym in Heqn; revert Heqn p; revert G v.
apply lt_wf_rect with (n:=n); clear n; intros n IH G v G_size p.
destruct p.
- exists (path_stop _ _ e); simpl; lia.
- assert(length (remove dec w G) < n).
  rewrite <-G_size; apply remove_length_lt, i.
  eapply path_pop, IH in p as [p Hp]. 3: reflexivity. 2: easy.
  destruct path_subset with (p:=p)(H:=G) as [q q_len].
  intros; apply in_remove in H0; easy.
  exists (path_step _ v w i i0 q). simpl; lia.
Qed.

End Connecting_paths.

Arguments path {_}.
Arguments path_length {_ _ _ _ _}.
Arguments Connected {_}.
