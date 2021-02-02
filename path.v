(* Theorems about connections in finite graphs. *)

Require Import Utf8 PeanoNat Wf_nat List Lia.
From larith Require Import tactics notations utilities.

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

Lemma path_subset G H v :
  path G v -> (∀x, In x G -> In x H) -> path H v.
Proof.
intros p subset; induction p.
now apply path_stop. eapply path_step.
apply subset, i. all: easy.
Qed.

Lemma Connected_split G Ga Gb v :
  Connected G v -> (∀x, In x G <-> In x Ga \/ In x Gb) ->
  Exists (Connected Ga) Gb \/ Connected Ga v.
Proof.
intros [p] g_spec; induction p.
- right; apply conn, path_stop, e.
- destruct IHp. now left. destruct H.
  apply g_spec in i as [H1|H2].
  + right; now apply conn, path_step with (w:=w).
  + left; apply Exists_exists; exists w; split.
    easy. apply conn, X.
Qed.

(* We can effectively determine if v is connected to an end node. *)
Theorem Connected_dec G v :
  {Connected G v} + {¬Connected G v}.
Proof.
remember (length G) as n; revert Heqn; revert G v.
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
    unfold G'; rewrite G_size, subtract_length.
    fold Gv; lia.
  + (* A path exists. *)
    left. apply Exists_exists in e as [w [H1w [p]]].
    apply intersect_spec in H1w.
    apply conn, path_step with (w:=w); try easy.
    eapply path_subset. apply p.
    intros; eapply subtract_spec, H0.
  + (* Any path would yield a contradiction. *)
    right. intros Hv; apply n2.
    apply Connected_split with (Ga:=G')(Gb:=Gv) in Hv as [Hv|[p]].
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

(* A path can be shortened to at most the size of the graph. *)
Theorem short_path G v (p : path G v) :
  Σ q : path G v, path_length q <= length G.
Proof.
Admitted.

End Connecting_paths.

Arguments path {_}.
Arguments path_length {_ _ _ _ _}.
Arguments Connected {_}.
