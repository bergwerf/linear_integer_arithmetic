(* A depth-first search algorithm. *)

Require Import Utf8 List.
From larith Require Import tactics notations utilities.
Import ListNotations.

Section Related_elements.

Variable X : Type.
Variable R : X -> X -> Prop.

Inductive Related : list X -> Prop :=
  | related_nil : Related []
  | related_one x : Related [x]
  | related_cons x y l : Related (y :: l) -> R x y -> Related (x :: y :: l).

End Related_elements.

Arguments Related {_}.

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

Definition Path := Related (λ v w, In w (adj v)).
Notation diff x y := (subtract dec x y).
Notation Inl x := (∃l, x = inl l).

Definition DFS_path visited tr :=
  Path tr /\ NoDup tr /\ Forall (λ v, ¬In v visited) tr.
Definition DFS_solution visited v tr :=
  DFS_path visited (v :: tr) /\ accept (last tr v) = true.

Theorem dfs_sound depth visited v tr :
  dfs depth visited v = inr tr ->
  DFS_solution visited v tr.
Proof.
revert visited v tr; induction depth; simpl; intros. easy.
destruct (in_dec dec v visited). easy.
destruct (accept v) eqn:C.
- inv H; repeat split. apply related_one.
  apply NoDup_cons; [easy|apply NoDup_nil].
  apply Forall_cons; easy. apply C.
- destruct (search _) eqn:Hs. easy. destruct p as [v' tr']; inv H.
  apply search_sound with (P:=DFS_solution (v :: visited)) in Hs.
  (* search_sound is not strong enough to handle cascading states. *)
Admitted.

Variable graph : list node.
Hypothesis graph_spec : ∀v, In v graph.

Theorem dfs_complete visited v :
  Inl (dfs (length (diff graph visited)) visited v) ->
  ¬∃tr, DFS_solution visited v tr.
Proof.
Admitted.

End Depth_first_search.

Arguments dfs {_}.
