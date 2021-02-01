(* Theorems about connections in finite graphs. *)

Require Import Utf8 PeanoNat Wf_nat List Lia.
From larith Require Import tactics notations utilities.

Section Path_predicate.

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
pose(gv := intersect dec g (adj v)).
destruct (Nat.eq_dec (length gv) 0).
- (* No path exists since g ∩ adj v = ∅. *)
  right; intros HC; inv HC. apply in_nil with (a:=w).
  apply length_zero_iff_nil in e; rewrite <-e.
  now apply intersect_spec.
- (* Show that g is not empty. *)
  assert(length g ≠ 0). {
    intros H; apply n1. unfold gv; rewrite intersect_length. lia. }
  (* Determine if a node in g ∩ adj v is connected through g \ adj v. *)
  pose(g' := subtract dec g (adj v)).
  destruct (Exists_dec (Path g') gv).
  + (* Decide using the induction hypothesis. *)
    intros; eapply IH. 2: reflexivity.
    unfold g'; rewrite g_len, subtract_length.
    fold gv; lia.
  + (* A path exists. *)
    left. apply Exists_exists in e as [w [H1w H2w]].
    apply intersect_spec in H1w.
    apply Path_step with (w:=w); try easy.
    eapply Path_subset. apply H2w.
    intros; eapply subtract_spec, H0.
  + (* Any path would yield a contradiction. *)
    right. intros Hv; apply n2.
    apply Path_split with (g1:=g')(g2:=gv) in Hv as [Hv|Hv].
    (* Either we find a path through g', or we find an impossible path. *)
    easy. exfalso; inv Hv. apply subtract_spec in H0; easy.
    (* Show that g = g1 ∪ g2. *)
    intros w; split; intros.
    * destruct (in_dec dec w (adj v)).
      right; now apply intersect_spec.
      left; now apply subtract_spec.
    * destruct H0.
      now apply subtract_spec in H0.
      now apply intersect_spec in H0.
Qed.

End Path_predicate.

Arguments Path {_}.
