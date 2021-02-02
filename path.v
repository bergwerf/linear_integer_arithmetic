(* Theorems about connections in finite graphs. *)

Require Import Utf8 PeanoNat Wf_nat List Lia.
From larith Require Import tactics notations utilities.

Section Graph_connectivity.

Variable node : Type.
Variable adj : node -> list node.
Variable End : node -> Prop.

Hypothesis dec : ∀v w : node, {v = w} + {v ≠ w}.
Hypothesis End_dec : ∀v, {End v} + {¬End v}.

(* A path to an end node in graph g. *)
Inductive path g : node -> Type :=
  | path_stop v : End v -> path g v
  | path_step v w : In w g -> In w (adj v) -> path g w -> path g v.

Inductive Connected g v : Prop :=
  | conn : path g v -> Connected g v.

Fixpoint path_length {g n} (p : path g n) : nat :=
  match p with
  | path_stop _ _ _ => 0
  | path_step _ _ _ _ _ q => S (path_length q)
  end.

Lemma path_subset g g' v :
  path g' v -> (∀x, In x g' -> In x g) -> path g v.
Proof.
intros p subset; induction p.
now apply path_stop. eapply path_step.
apply subset, i. all: easy.
Qed.

Lemma Connected_split g g1 g2 v :
  Connected g v -> (∀x, In x g <-> In x g1 \/ In x g2) ->
  Exists (Connected g1) g2 \/ Connected g1 v.
Proof.
intros [p] g_spec; induction p.
- right; apply conn, path_stop, e.
- destruct IHp. now left. destruct H.
  apply g_spec in i as [H1|H2].
  + right; now apply conn, path_step with (w:=w).
  + left; apply Exists_exists; exists w; split.
    easy. apply conn, X.
Qed.

Theorem Connected_dec g v :
  {Connected g v} + {¬Connected g v}.
Proof.
remember (length g) as n; revert Heqn; revert g v.
apply lt_wf_rect with (n:=n); clear n; intros n IH g v g_len.
(* Check if v is a target state. *)
destruct (End_dec v).
left; apply conn, path_stop, e.
(* Determine if there is an intersection between g and adj v. *)
pose(gv := intersect dec g (adj v)).
destruct (Nat.eq_dec (length gv) 0).
- (* No path exists since g ∩ adj v = ∅. *)
  right; intros [p]; inv p. apply in_nil with (a:=w).
  apply length_zero_iff_nil in e; rewrite <-e.
  now apply intersect_spec.
- (* Show that g is not empty. *)
  assert(length g ≠ 0). {
    intros H; apply n1. unfold gv; rewrite intersect_length. lia. }
  (* Determine if a node in g ∩ adj v is connected through g \ adj v. *)
  pose(g' := subtract dec g (adj v)).
  destruct (Exists_dec (Connected g') gv).
  + (* Decide using the induction hypothesis. *)
    intros; eapply IH. 2: reflexivity.
    unfold g'; rewrite g_len, subtract_length.
    fold gv; lia.
  + (* A path exists. *)
    left. apply Exists_exists in e as [w [H1w [p]]].
    apply intersect_spec in H1w.
    apply conn, path_step with (w:=w); try easy.
    eapply path_subset. apply p.
    intros; eapply subtract_spec, H0.
  + (* Any path would yield a contradiction. *)
    right. intros Hv; apply n2.
    apply Connected_split with (g1:=g')(g2:=gv) in Hv as [Hv|[p]].
    (* Either we find a path through g', or we find an impossible path. *)
    easy. exfalso; inv p. apply subtract_spec in H0; easy.
    (* Show that g = g1 ∪ g2. *)
    intros w; split; intros.
    * destruct (in_dec dec w (adj v)).
      right; now apply intersect_spec.
      left; now apply subtract_spec.
    * destruct H0.
      now apply subtract_spec in H0.
      now apply intersect_spec in H0.
Qed.

End Graph_connectivity.

Arguments path {_}.
Arguments path_length {_ _ _ _ _}.
Arguments Connected {_}.
