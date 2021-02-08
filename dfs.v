(* A depth-first search algorithm. *)

Require Import Utf8 Wf_nat List.
From larith Require Import tactics notations utilities.
Import ListNotations.

Section Reflexive_transitive_closure.

Variable X : Type.
Variable R : X -> X -> Prop.

Inductive RTC : list X -> Prop :=
  | rtc_refl x : RTC [x]
  | rtc_cons x y l : RTC (y :: l) -> R x y -> RTC (x :: y :: l).

Theorem RTC_trans l1 x1 x2 l2 :
  RTC (l1 ++ [x1]) -> RTC (x2 :: l2) -> R x1 x2 ->
  RTC (l1 ++ x1 :: x2 :: l2).
Proof.
induction l1; simpl; intros. apply rtc_cons; easy.
destruct l1; simpl in *; inv H; repeat apply rtc_cons.
4: apply IHl1. all: easy.
Qed.

End Reflexive_transitive_closure.

Arguments RTC {_}.

Section Stateful_search.

Variable X state solution : Type.
Variable check : state -> X -> state + solution.

Fixpoint search s l : state + (X × solution) :=
  match l with
  | []      => inl s
  | x :: l' =>
    match check s x with
    | inl s' => search s' l'
    | inr y  => inr (x, y)
    end
  end.

Section Soundness.

Variable P : X -> solution -> Prop.
Hypothesis check_sound : ∀s x sol, check s x = inr sol -> P x sol.

Theorem search_sound s l x sol :
  search s l = inr (x, sol) -> In x l /\ P x sol.
Proof.
revert s; induction l; simpl; intros. easy.
destruct (check s a) eqn:Ha.
apply IHl in H; split; [now right|apply H].
inv H; split; [now left|eapply check_sound, Ha].
Qed.

End Soundness.

End Stateful_search.

Arguments search {_ _ _}.

Section Depth_first_search.

Variable node : Type.
Variable adj : node -> list node.
Variable accept : node -> bool.
Hypothesis dec : ∀v w : node, {v = w} + {v ≠ w}.

Fixpoint dfs depth visited v : list node + list node :=
  match depth with
  | 0   => inl visited
  | S n =>
    if in_dec dec v visited then inl visited
    else if accept v then inr []
    else match search (dfs n) (v :: visited) (adj v)
    with
    | inl vis     => inl vis
    | inr (w, tr) => inr (w :: tr)
    end
  end.

Notation diff x y := (subtract dec x y).
Notation Inr x := (∃r, x = inr r).
Notation Path := (RTC (λ v w, In w (adj v))).

Definition DFS_solution_weak v tr :=
  Path (v :: tr) /\ accept (last tr v) = true.
Definition DFS_solution visited v tr :=
  DFS_solution_weak v tr /\ Forall (λ v, ¬In v visited) (v :: tr).

Theorem dfs_sound_weak depth visited v tr :
  dfs depth visited v = inr tr -> DFS_solution_weak v tr.
Proof.
revert visited v tr; induction depth; simpl; intros. easy.
destruct (in_dec dec v visited). easy.
destruct (accept v) eqn:C. inv H; split; [apply rtc_refl|apply C].
destruct (search _) eqn:Hs. easy. destruct p as [v' tr']; inv H.
apply search_sound with (P:=DFS_solution_weak) in Hs as [H []].
split. apply rtc_cons; easy. rewrite last_cons; apply H1.
apply IHdepth.
Qed.

Variable graph : list node.
Hypothesis graph_spec : ∀v, In v graph.

Theorem dfs_complete visited v tr :
  DFS_solution visited v tr ->
  Inr (dfs (length (diff graph visited)) visited v).
Proof.
remember (length (diff graph visited)) as n eqn:len;
revert len; revert visited v tr.
apply lt_wf_rect with (n:=n); clear n; intros; destruct n.
- (* Contradition; v ∈ graph \ visited. *)
  destruct H0 as [_ H0]; inv H0.
  exfalso; apply in_nil with (a:=v).
  apply eq_sym, length_zero_iff_nil in len; rewrite <-len.
  apply subtract_spec; easy.
- (* The search through (adj v) must yield a solution. *)
  destruct H0; inv H1; simpl.
  destruct (in_dec _) as [F|_]; [easy|].
  destruct (accept v) eqn:Hv; [now exists []|].
Admitted.

End Depth_first_search.

Arguments dfs {_}.
