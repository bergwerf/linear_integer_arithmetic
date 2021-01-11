(* Lemmas on various topics. *)

Require Import Utf8 PeanoNat List Lia.
From larith Require Import tactics notations.
Import ListNotations.

Section Laws_of_logic.

Section Propositions.

Variable P Q : Prop.

Lemma triple_not :
  ¬¬¬P -> ¬P.
Proof.
auto.
Qed.

Lemma weaken :
  P -> ¬¬P.
Proof.
auto.
Qed.

Lemma contra :
  (P -> Q) -> (¬Q -> ¬P).
Proof.
auto.
Qed.

Lemma not_or_and :
  ¬(P \/ Q) <-> ¬P /\ ¬Q.
Proof.
split; auto. now intros [H1 H2] [H|H].
Qed.

Variable P_dec : {P} + {¬P}.
Variable Q_dec : {Q} + {¬Q}.

End Propositions.

End Laws_of_logic.

Section Lemmas_about_lists.

Lemma list_prod_nil_r {X Y} (l : list X) :
  @list_prod X Y l nil = nil.
Proof.
now induction l.
Qed.

Lemma list_prod_single {X Y} (x : X) (y : Y) :
  [(x, y)] = list_prod [x] [y].
Proof.
easy.
Qed.

Lemma list_singleton {X} (l : list X) :
  length l = 1 -> ∃x, l = [x].
Proof.
intros. destruct l. easy. destruct l.
now exists x. easy.
Qed.

(* Construct a powerset. *)
Theorem list_powerset {X} (l : list X) :
  (∀x y : X, {x = y} + {x ≠ y}) ->
  Σ L, length L = 2^length l /\
  ∀s, (∀x, In x s -> In x l) <->
  ∃t, In t L /\ ∀x, In x s <-> In x t.
Proof.
intros dec; induction l.
- exists [[]]; repeat split; simpl.
  + intros H; exists []; split. now left.
    split; intros. exfalso; eapply H, H0. easy.
  + intros [t [H1 H2]]. destruct H1.
    subst; intros. now apply H2 in H. easy.
- destruct IHl as [L [L_len HL]].
  exists (L ++ map (cons a) L); repeat split.
  + rewrite app_length, map_length, L_len; simpl; lia.
  + intros Hs; pose(s' := remove dec a s).
    destruct (proj1 (HL s')) as [t Ht].
    intros. apply in_remove in H as [H1 H2].
    apply Hs in H1; inv H1; easy.
    destruct (in_dec dec a s).
    * exists (a :: t); split. apply in_app_iff; right.
      apply in_map_iff; now exists t.
      intros; split; intros. destruct (dec x a).
      subst; apply in_eq. eapply in_cons, Ht. now apply in_in_remove.
      inv H. apply Ht in H0. eapply in_remove, H0.
    * exists t; split. apply in_app_iff; left. easy.
      eapply notin_remove in n; rewrite <-n; apply Ht.
  + intros [t [H1 H2]]. apply in_app_or in H1 as [H1|H1]; intros.
    * eapply in_cons, HL. 2: apply H. now exists t.
    * apply in_map_iff in H1 as [t' [H1a H1b]]; subst.
      apply H2 in H; inv H. apply in_eq. apply in_cons.
      eapply HL. 2: apply H0. now exists t'.
Qed.

Section Witness_list.

Variable X Y : Type.
Variable R : X -> Y -> Prop.
Hypothesis ex : ∀x, ∃y : Y, R x y.

Theorem witness_list xs :
  ∃ys, Forall2 R xs ys.
Proof.
induction xs. now exists [].
destruct (ex a) as [y Hy];
destruct (IHxs) as [ys H].
exists (y :: ys); now apply Forall2_cons.
Qed.

Theorem Forall2_in_l xs ys x :
  In x xs -> Forall2 R xs ys -> ∃y, In y ys /\ R x y.
Proof.
revert ys; induction xs; simpl; intros. easy.
destruct ys; simpl in *. easy. inv H0; destruct H.
- subst; exists y; split. apply in_eq. easy.
- eapply IHxs in H as [y' Hy']. 2: apply H6.
  exists y'; split. now right. easy.
Qed.

Theorem Forall2_swap xs ys :
  Forall2 R xs ys -> Forall2 (λ y x, R x y) ys xs.
Proof.
revert ys; induction xs; destruct ys; simpl; intros. 1-3: easy.
inv H; apply Forall2_cons. easy. apply IHxs, H5.
Qed.

End Witness_list.

Corollary Forall2_in_r {X Y} (xs : list X) (ys : list Y) R y :
  In y ys -> Forall2 R xs ys -> ∃x, In x xs /\ R x y.
Proof.
intros Hy H; apply Forall2_swap in H.
eapply Forall2_in_l in H as [x Hx].
exists x; apply Hx. easy.
Qed.

Section Option_list_filtering.

Variable X : Type.

Fixpoint remove_None (l : list (option X)) :=
  match l with
  | [] => []
  | None :: l' => remove_None l'
  | Some x :: l' => x :: remove_None l'
  end.

Lemma remove_None_map_Some l :
  remove_None (map Some l) = l.
Proof.
induction l; simpl.
easy. now rewrite IHl.
Qed.

Lemma remove_None_app l l' :
  remove_None (l ++ l') = remove_None l ++ remove_None l'.
Proof.
induction l as [|[x|] l]; simpl. easy.
now rewrite IHl. apply IHl.
Qed.

End Option_list_filtering.

End Lemmas_about_lists.

Arguments remove_None {_}.
