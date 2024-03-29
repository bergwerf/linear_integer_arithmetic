(* A depth-first search algorithm. *)

Require Import PeanoNat.
From larith Require Import A_setup B1_utils.

Section Stateful_search.

Variable X state solution : Type.
Variable check : state -> X -> state + solution.

Fixpoint search s l : state + (X × solution) :=
  match l with
  | []      => inl s
  | x :: l' =>
    match check s x with
    | inl t => search t l'
    | inr y => inr (x, y)
    end
  end.

Theorem search_app s l1 l2 :
  search s (l1 ++ l2) =
  match search s l1 with
  | inl t => search t l2
  | _     => search s l1
  end.
Proof.
revert s; induction l1; simpl; intros. easy.
destruct (check s a); [apply IHl1|easy].
Qed.

Theorem search_inr_inv s l x y :
  search s l = inr (x, y) -> In x l /\ ∃t, check t x = inr y.
Proof.
revert s; induction l; simpl; intros. easy.
destruct (check s a) as [t|y'] eqn:Ha.
apply IHl in H; split; [now right|apply H].
inv H; split; [now left|exists s; apply Ha].
Qed.

End Stateful_search.

Arguments search {_ _ _}.

Section Depth_first_search.

Variable node : Type.
Variable adj : node -> list node.
Variable accept : node -> bool.
Hypothesis dec : ∀v w : node, {v = w} + {v ≠ w}.

Notation diff x y := (subtract dec x y).
Notation next v := (remove dec v (adj v)).
Notation Path := (RTC (λ v w, In w (next v))).
Notation Notin l := (λ x, ¬In x l).
Notation Inr x := (∃r, x = inr r).

Fixpoint dfs depth visited v : list node + list node :=
  match depth with
  | 0   => inl visited
  | S n =>
    if in_dec dec v visited then inl visited
    else if accept v then inr []
    else match search (dfs n) (v :: visited) (next v)
    with
    | inl visited'  => inl visited'
    | inr (w, path) => inr (w :: path)
    end
  end.

Definition DFS_path visited path :=
  Path path /\ Forall (Notin visited) path.
Definition DFS_solution visited v path :=
  DFS_path visited (v :: path) /\ accept (last path v) = true.

Section Utilities.

Theorem Inr_inr {X Y} y :
  Inr (@inr X Y y).
Proof.
exists y; reflexivity.
Qed.

Theorem DFS_solution_refl visited v :
  ¬In v visited /\ accept v = true <-> DFS_solution visited v [].
Proof.
split.
- repeat split. apply RTC_refl.
  apply Forall_cons; easy. simpl; apply H.
- intros [[]]; inv H0.
Qed.

Theorem DFS_path_cons visited v w path :
  DFS_path visited (w :: path) /\ ¬In v visited /\ In w (next v) <->
  DFS_path visited (v :: w :: path).
Proof.
split.
- intros [[] []]; repeat split.
  apply RTC_cons; easy. apply Forall_cons; easy.
- intros []; inv H; inv H0.
Qed.

Theorem DFS_path_incl vis_a vis_b path :
  (∀v, In v vis_a -> In v vis_b) ->
  DFS_path vis_b path -> DFS_path vis_a path.
Proof.
split. apply H0.
eapply Forall_impl. 2: apply H0.
intros v; apply contra, H.
Qed.

Corollary DFS_solution_cons visited v w path :
  DFS_solution visited w path /\ ¬In v visited /\ In w (next v) <->
  DFS_solution visited v (w :: path).
Proof.
unfold DFS_solution; rewrite <-DFS_path_cons, last_cons; easy.
Qed.

Corollary DFS_global_solution_refl v :
  accept v = true <-> DFS_solution [] v [].
Proof.
rewrite <-DFS_solution_refl; easy.
Qed.

Corollary DFS_global_solution_cons v w path :
  DFS_solution [] w path /\ In w (next v) <->
  DFS_solution [] v (w :: path).
Proof.
rewrite <-DFS_solution_cons; easy.
Qed.

End Utilities.

Section Soundness.

(* Visited nodes are remembered. *)
Lemma dfs_inl_incl n vis_a v vis_z z :
  dfs n vis_a v = inl vis_z -> In z vis_a -> In z vis_z.
Proof.
revert vis_a v vis_z; induction n; simpl; intros. inv H.
destruct (in_dec _); [inv H|].
destruct (accept v); [easy|].
destruct (search _) as [vis_z'|[]] eqn:Hs; [inv H|easy].
remember (v :: vis_a) as vis_b.
assert(In z vis_b) by (subst; apply in_cons, H0).
clear H0 Heqvis_b; revert H Hs; revert vis_b.
induction (next v) as [|w ws]; simpl; intros.
inv Hs. destruct (dfs _) as [vis_c|] eqn:Hw; [|easy].
(* The inclusion relation is preserved over the induction. *)
destruct (in_dec dec z vis_c); [|exfalso].
apply IHws with (vis_b:=vis_c); easy.
apply IHn in Hw; easy.
Qed.

(* Solutions given by dfs are correct. *)
Theorem dfs_sound n vis_a v path :
  dfs n vis_a v = inr path -> DFS_solution vis_a v path.
Proof.
revert vis_a v path; induction n; simpl; intros. easy.
destruct (in_dec _); [easy|].
destruct (accept v) eqn:Hv. inv H.
repeat split; [apply RTC_refl|apply Forall_cons; easy|apply Hv].
destruct (search _) as [|[z from_z]] eqn:Hs; [easy|inv H].
(* Abstract over (v :: vis_a) and (next v). *)
remember (v :: vis_a) as vis_b; remember (next v) as nextv.
assert(∀x, In x vis_a -> In x vis_b) by (intros; subst; apply in_cons, H).
assert(∀x, In x nextv -> In x (next v)) by (subst; easy).
clear Hv Heqvis_b Heqnextv; revert Hs H H0; revert vis_b.
(* Do induction over nextv. *)
induction nextv as [|w ws]; simpl; intros.
easy. destruct (dfs _) as [vis_c|] eqn:Hw.
- apply IHws in Hs. apply Hs.
  intros; eapply dfs_inl_incl. apply Hw. apply H, H1.
  intros; apply H0; right; apply H1.
- inv Hs; apply IHn in Hw.
  apply DFS_solution_cons; split; split.
  eapply DFS_path_incl; [apply H|apply Hw].
  apply Hw. apply n0. apply H0; left; easy.
Qed.

End Soundness.

Section Completeness.

Variable graph : list node.
Hypothesis graph_spec : ∀v, In v graph.

(* Two DFS paths can be appended. *)
Lemma DFS_path_trans visited v path1 path2 :
  DFS_path visited (v :: path1) ->
  DFS_path visited (last path1 v :: path2) ->
  DFS_path visited (v :: path1 ++ path2).
Proof.
intros [H1a H1b] [H2a H2b].
rewrite app_comm_cons; split. eapply RTC_trans with (d:=v).
apply H1a. rewrite last_cons; apply H2a.
apply Forall_app; split; [apply H1b|inv H2b].
Qed.

(* Each new visited node can be reached by a path. *)
Lemma path_to_visited n vis_a v vis_z z :
  dfs n vis_a v = inl vis_z -> ¬In z vis_a -> In z vis_z ->
  ∃path, DFS_path vis_a (v :: path) /\ last path v = z.
Proof.
revert vis_a v vis_z; induction n; simpl; intros. inv H.
destruct (in_dec _); [inv H|].
destruct (accept v); [easy|].
destruct (search _) as [vis_z'|[]] eqn:Hs; [inv H|easy].
(* Discard the case z = v. *)
destruct (dec z v). exists []; subst; repeat split.
apply RTC_refl. apply Forall_cons; easy.
(* Abstract over (v :: vis_a) and (next v). *)
remember (v :: vis_a) as vis_b; remember (next v) as nextv.
assert(¬In z vis_b) by (subst; apply not_in_cons; easy).
assert(∀x, In x vis_a -> In x vis_b) by (intros; subst; apply in_cons, H2).
assert(∀x, In x nextv -> In x (next v)) by (subst; easy).
clear H0 n1 Heqvis_b Heqnextv; revert Hs H H2; revert vis_b.
induction nextv as [|w ws]; simpl; intros. inv Hs. 
(* Destruct the recursive call, and check if it visits z. *)
destruct (dfs _) as [vis_c|] eqn:Hw; [|easy].
destruct (in_dec dec z vis_c).
- (* If the recursive call visits z; use IHn. *)
  apply IHn in Hw as [path []]; try easy.
  exists (w :: path); split; [|rewrite last_cons; apply H4].
  apply DFS_path_cons; split. eapply DFS_path_incl; [apply H2|apply H0].
  split. apply n0. apply H3, in_eq.
- (* If it doesn't; use IHnextv. *)
  apply IHws with (vis_b:=vis_c); try easy.
  intros; apply H3; apply in_cons, H0.
  intros; eapply dfs_inl_incl. apply Hw. apply H2, H0.
Qed.

(* If a solution exists, then, given enough fuel, dfs will also find one. *)
Theorem dfs_complete vis_a n :
  length (diff graph vis_a) <= n ->
  ∀v path, DFS_solution vis_a v path -> Inr (dfs n vis_a v).
Proof.
revert vis_a; induction n; intros vis_a Hn; intros.
(* Zero case. Contradition since v ∈ graph \ visited. *)
destruct H as [[_ H]]; inv H.
exfalso; apply in_nil with (a:=v).
apply Nat.le_0_r, length_zero_iff_nil in Hn.
rewrite <-Hn; apply subtract_spec; easy.
(* Successor case. *)
destruct H as [[]]; inv H0; simpl.
destruct (in_dec _); [easy|]; clear n0.
destruct (accept v) eqn:Hv; [apply Inr_inr|].
(* Get a sub-path without v. *)
destruct split_at_last_instance with (x:=v)(l:=v::path)
as [pre [path' []]]. apply dec. apply in_eq.
rewrite <-last_cons with (d:=v) in H1; rewrite H0 in H, H1.
apply RTC_app_inv in H as [_ H]; rewrite last_app in H1.
assert(Forall (Notin vis_a) path'). {
  destruct pre; inv H0. apply Forall_app in H5 as [_ H5]; inv H5. }
clear H0 H5 path pre.
(* The given path cannot be empty; obtain the next node. *)
inv H3; [simpl in H1; rewrite H1 in Hv; easy|].
inv H; rewrite last_cons in H1; apply in_remove in H9 as ?.
rename x into w, l into path.
(* Wrap hypotheses back together and clean up. *)
assert(H' : DFS_solution (v :: vis_a) w path). {
  repeat split; try easy. apply Forall_cons.
  apply not_in_cons; easy. apply not_in_cons in H2.
  apply Forall_forall; intros u Hu [F|F]; subst. easy.
  eapply Forall_forall with (x:=u) in H5; easy. }
assert(Hn' : length (diff graph (v :: vis_a)) <= n). {
  simpl; eapply Nat.lt_succ_r, Nat.lt_le_trans.
  apply subtract_length_lt_cons_r; [apply graph_spec|apply H4]. apply Hn. }
clear H H0 H1 H2 H4 H5 H7 Hv Hn.
remember (v :: vis_a) as vis_b; clear Heqvis_b vis_a.
(* Split (next v) into (next1 ++ w :: next2). *)
apply split_list in H9 as [next1 [next2 H9]]; rewrite H9.
cut(Inr (search (dfs n) vis_b (next1 ++ [w]))). intros [[w' path']].
rewrite cons_app, app_assoc, search_app, H; apply Inr_inr.
clear H9 v; revert H' Hn'; revert vis_b.
(* Do induction on the nodes that are checked before w. *)
induction next1 as [|u]; simpl; intros.
- (* At w the previous induction hypothesis guarantees a solution. *)
  apply IHn in H' as [path' H']. rewrite H'; apply Inr_inr. easy.
- (* Check if the search terminates before w. *)
  destruct (dfs _) as [vis_c|] eqn:Hu; [|apply Inr_inr].
  (* If not, then we can use IHnext1. *)
  apply IHnext1; clear IHnext1 next1.
  + (* Show that the path does not go through visited nodes. *)
    destruct H' as [[]]; repeat split; try easy.
    rewrite Forall_Exists_neg, Exists_exists; intros [e [H1e H2e]].
    apply Forall_forall with (x:=e) in H0 as H3e; [|apply H1e].
    (* If it does, then there exists a contradictory solution for v. *)
    eapply path_to_visited in H2e as [to_e ?]; [|apply Hu|apply H3e].
    destruct H2; subst. apply split_list in H1e as [path1 [path2 H1e]].
    rewrite <-last_cons with (d:=w) in H1; rewrite H1e in H, H0, H1.
    apply RTC_app_inv in H as [_ H]; apply Forall_app in H0 as [_ H0];
    rewrite last_app in H1.
    (* to_e ++ path2 is now a solution for u. *)
    assert(DFS_solution vis_b u (to_e ++ path2)).
    * split. apply DFS_path_trans; easy.
      destruct path2. rewrite app_nil_r; apply H1.
      rewrite last_app; rewrite last_cons in H1; apply H1.
    * apply IHn in H3. rewrite Hu in H3; destruct H3; easy. easy.
  + (* Show that n is big enough. *)
    etransitivity; [|apply Hn'].
    apply length_subtract_le_incl_r.
    intros; eapply dfs_inl_incl; [apply Hu|apply H].
Qed.

End Completeness.

Variable upper_bound : nat.
Hypothesis finite_graph : ∃l, length l <= upper_bound /\ ∀v : node, In v l.

Theorem depth_first_search visited v :
  (Σ path, DFS_solution visited v path) +
  {∀path, ¬DFS_solution visited v path}.
Proof.
destruct (dfs upper_bound visited v) as [visited'|path] eqn:H.
- right; intros path Hpath.
  destruct finite_graph as [graph [graph_len graph_spec]].
  assert(Hlen : length (diff graph visited) <= upper_bound).
  + rewrite subtract_length; etransitivity.
    apply Nat.le_sub_l. apply graph_len.
  + eapply dfs_complete with (v:=v) in Hlen as [path' H'].
    congruence. apply graph_spec. apply Hpath.
- left; exists path. eapply dfs_sound, H.
Defined.

End Depth_first_search.

Arguments dfs {_}.
Arguments DFS_path {_}.
Arguments DFS_solution {_}.
