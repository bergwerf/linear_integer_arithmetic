(* Basic utilities for various purposes. *)

Require Import Utf8 PeanoNat List Lia.
From larith Require Import tactics notations.
Import ListNotations.

(******************************************************************************)
(* I. Laws of constructive propositional and predicate logic.                 *)
(******************************************************************************)
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

Lemma not_dec :
  {¬P} + {¬¬P}.
Proof.
destruct P_dec; auto.
Qed.

Lemma and_dec :
  {P /\ Q} + {¬(P /\ Q)}.
Proof.
destruct P_dec, Q_dec.
now left. all: now right.
Qed.

End Propositions.

End Laws_of_logic.

(******************************************************************************)
(* II. Various list utilities.                                               *)
(******************************************************************************)
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

Section List_constructions_using_decidability.

Variable X : Type.
Hypothesis dec : ∀x y : X, {x = y} + {x ≠ y}.

Section Powerset_with_canonical_elements.

(* Construct a powerset that can effectively give canonical members. *)
Theorem list_powerset (l : list X) :
  Σ Pl, (length Pl = 2^length l) ×
    ((∀s, (∀x, In x s -> In x l) -> Σ t, In t Pl /\ ∀x, In x s <-> In x t) ×
    (∀s x, In s Pl -> In x s -> In x l)).
Proof.
(*
To find a canonical element, this program essentially breaks down a given
list in the order given by l. For each element it remembers if it was in the
list and then removes it from the list for a recursive call. The list is then
rebuilt in the same order as l. A more efficient approach could:
- Use an ordering to sort the list (but the improvement here is unclear).
- Represent sets as trees, or as l zipped with some list of booleans.
  Here every element might be a canonical element.
*)
induction l.
- exists [[]]; repeat split; simpl.
  + intros s H; exists []; split. now left.
    split; intros. exfalso; eapply H, H0. easy.
  + intros s x [H|H]. now subst. easy.
- destruct IHl as [Pl [Pl_len [IH1 IH2]]].
  exists (Pl ++ map (cons a) Pl); repeat split.
  + rewrite app_length, map_length, Pl_len; simpl; lia.
  + intros s Hs; pose(s' := remove dec a s).
    destruct (IH1 s') as [t Ht].
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
  + intros s x H. apply in_app_or in H as [H|H]; intros.
    * eapply in_cons, IH2. apply H. easy.
    * apply in_map_iff in H as [t [R H]]; subst.
      inv H0. apply in_eq. eapply in_cons, IH2. apply H. easy.
Qed.

End Powerset_with_canonical_elements.

Section Filter_by_a_predicate.

Variable P : X -> Prop.
Hypothesis P_dec : ∀x, {P x} + {¬P x}.

Fixpoint pfilter (l : list X) :=
  match l with
  | [] => []
  | x :: l' => if P_dec x then x :: pfilter l' else pfilter l'
  end.

Theorem pfilter_spec l x :
  In x (pfilter l) <-> In x l /\ P x.
Proof.
induction l; simpl. easy.
destruct (P_dec a); simpl; split; intros.
all: try split; repeat destruct H; subst.
all: try apply IHl in H; try easy; auto.
now right. right; apply IHl; easy. now right. now apply IHl.
Qed.

Theorem pfilter_length l :
  length (pfilter l) <= length l.
Proof.
induction l; simpl. easy.
destruct (P_dec a); simpl; lia.
Qed.

End Filter_by_a_predicate.

Section List_intersection_and_subtraction.

Variable l l' : list X.

Definition list_isect :=
  pfilter (λ x, In x l') (λ x, in_dec dec x l') l.

Definition list_subt :=
  pfilter (λ x, ¬In x l') (λ x, not_dec _ (in_dec dec x l')) l. 

Corollary list_isect_spec x :
  In x list_isect <-> In x l /\ In x l'.
Proof.
apply pfilter_spec.
Qed.

Corollary list_subt_spec x :
  In x list_subt <-> In x l /\ ¬In x l'.
Proof.
apply pfilter_spec.
Qed.

Theorem list_subt_length :
  length list_subt = length l - length list_isect.
Proof.
unfold list_subt, list_isect; induction l; simpl pfilter. easy.
destruct (in_dec dec a l'), (not_dec _ _); try easy.
simpl length; rewrite IHl0; clear IHl0. remember (pfilter _ _ l0) as l1.
assert(length l1 <= length l0) by (subst; apply pfilter_length). lia.
Qed.

Corollary list_isect_length :
  length list_isect = length l - length list_subt.
Proof.
rewrite list_subt_length.
assert(length list_isect <= length l) by apply pfilter_length. lia.
Qed.

End List_intersection_and_subtraction.

End List_constructions_using_decidability.

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

Section Nth_element_of_a_mapped_list.

Variable X Y : Type.
Variable f : X -> Y.

Lemma nth_map i Γ d x :
  nth i Γ d = x -> nth i (map f Γ) (f d) = f x.
Proof.
revert i; induction Γ; destruct i; simpl.
1-3: congruence. apply IHΓ.
Qed.

Hypothesis f_inj : ∀x x', f x = f x' -> x = x'.

Lemma nth_map_inj i Γ d x :
  nth i (map f Γ) (f d) = f x -> nth i Γ d = x.
Proof.
revert i; induction Γ; destruct i; simpl.
1-3: apply f_inj. apply IHΓ.
Qed.

End Nth_element_of_a_mapped_list.

End Lemmas_about_lists.

Arguments list_isect {_}.
Arguments list_subt {_}.
Arguments remove_None {_}.
