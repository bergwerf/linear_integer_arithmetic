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
Variable Solution : X -> solution -> Prop.

Hypothesis check_sound : ∀s x sol, check s x = inr sol -> Solution x sol.

Fixpoint search s l : state + (X × solution) :=
  match l with
  | []      => inl s
  | x :: l' =>
    match check s x with
    | inl s' => search s' l'
    | inr y  => inr (x, y)
    end
  end.

Theorem search_sound s l x sol :
  search s l = inr (x, sol) -> In x l /\ Solution x sol.
Proof.
revert s; induction l; simpl; intros. easy.
destruct (check s a) eqn:Ha.
apply IHl in H; split; [now right|apply H].
inv H; split; [now left|eapply check_sound, Ha].
Qed.

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
    | inl vis      => inl vis
    | inr (w, tr) => inr (w :: tr)
    end
  end.

Definition Trace := Related (λ v w, In w (adj v)).
Definition Blind vis v := ∀tr, Trace (v :: tr) -> ∃w, In w tr /\ In w vis.

Theorem dfs_inr depth visited v tr :
  dfs depth visited v = inr tr -> Trace (v :: tr) /\ accept (last tr v) = true.
Proof.
revert visited v tr; induction depth; simpl; intros. easy.
destruct (in_dec dec v visited). easy.
destruct (accept v) eqn:C. inv H; split; [apply related_one|apply C].
destruct (search _) eqn:Hs. easy. destruct p as [v' tr']; inv H.
eapply search_sound in Hs. 2: intros; eapply IHdepth, H.
simpl in Hs; split. apply related_cons; easy.
rewrite last_cons; apply Hs.
Qed.

Theorem dfs_inl depth visited v vis :
  dfs depth visited v = inl vis ->
  Forall (Blind visited) (subtract dec vis visited).
Proof.
Admitted.

End Depth_first_search.

Arguments dfs {_}.
