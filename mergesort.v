(* A merge-sort algorithm. *)
(* Initial author: Hugo Herbelin, Oct 2009 *)
(* Altered to the style of this repository. *)

Require Import Utf8 List Permutation.
From larith Require Import tactics notations utilities.
Import ListNotations.

Notation Sorted leb := (RTC (λ x y, leb x y = true)). 

Section Merge_sort.

Variable X : Type.
Variable leb : X -> X -> bool.

Fixpoint merge l1 l2 :=
  let fix merge_aux l2 :=
  match l1, l2 with
  | [], _ => l2
  | _, [] => l1
  | x1 :: l1', x2 :: l2' =>
    if leb x1 x2
    then x1 :: merge l1' l2
    else x2 :: merge_aux l2'
  end
  in merge_aux l2.

Fixpoint merge_push stack l :=
  match stack with
  | [] => [Some l]
  | None :: stack' => Some l :: stack'
  | Some l' :: stack' => None :: merge_push stack' (merge l' l)
  end.

Fixpoint merge_all stack :=
  match stack with
  | [] => []
  | None :: stack' => merge_all stack'
  | Some l :: stack' => merge l (merge_all stack')
  end.

Fixpoint merge_iter stack l :=
  match l with
  | [] => merge_all stack
  | x :: l' => merge_iter (merge_push stack [x]) l'
  end.

Definition merge_sort := merge_iter [].

(** The proof of correctness *)

Notation Sorted := (Sorted leb).
Notation Sorted_stack stack := (Forall Sorted (strip stack)).
Notation flatten stack := (concat (strip stack)).

Notation "x <= y" := (leb x y = true) (at level 70).
Notation "x > y" := (leb x y = false) (at level 70).

Hypothesis leb_total : ∀x y, x <= y \/ y <= x.

Local Lemma leb_false x y :
  x > y -> y <= x.
Proof.
destruct (leb_total y x); [easy|congruence].
Qed.

Section Sorted.

Theorem Sorted_merge l1 l2 :
  Sorted l1 -> Sorted l2 -> Sorted (merge l1 l2).
Proof.
revert l2; induction l1; induction l2; intros; simpl; auto.
destruct (leb a a0) eqn:Heq1.
- inv H. simpl; apply RTC_cons; easy.
  assert(IH := IHl1 _ H3 H0); simpl; simpl in IH.
  destruct (leb y a0); apply RTC_cons; easy.
- apply leb_false in Heq1.
  inv H0. apply RTC_cons; easy.
  assert(IH := IHl2 H H3); simpl; simpl in IH.
  destruct (leb a y); apply RTC_cons; easy.
Qed.

Theorem Sorted_stack_merge_push stack l :
  Sorted_stack stack -> Sorted l -> Sorted_stack (merge_push stack l).
Proof.
revert l; induction stack as [|[|]]; intros; simpl.
1,3: constructor; easy. inv H. apply IHstack. easy.
apply Sorted_merge; easy.
Qed.

Theorem Sorted_stack_merge_all stack :
  Sorted_stack stack -> Sorted (merge_all stack).
Proof.
induction stack as [|[|]]; simpl; intros. constructor.
inv H; apply Sorted_merge. all: auto.
Qed.

Theorem Sorted_merge_iter stack l :
  Sorted_stack stack -> Sorted (merge_iter stack l).
Proof.
revert stack; induction l; simpl; intros.
apply Sorted_stack_merge_all, H.
apply IHl, Sorted_stack_merge_push. easy. constructor.
Qed.

Theorem Sorted_merge_sort l :
  Sorted (merge_sort l).
Proof.
apply Sorted_merge_iter; constructor.
Qed.

End Sorted.

Section Permutation.

Theorem Permutation_merge l1 l2 :
  Permutation (l1 ++ l2) (merge l1 l2).
Proof.
revert l2; induction l1; simpl merge; intros.
- destruct l2; apply Permutation_refl.
- induction l2. rewrite app_nil_r; apply Permutation_refl.
  destruct (leb a a0). apply perm_skip, IHl1.
  apply Permutation_sym, Permutation_cons_app, Permutation_sym, IHl2.
Qed.

Theorem Permutation_merge_push stack l :
  Permutation (l ++ flatten stack) (flatten (merge_push stack l)).
Proof.
revert l; induction stack as [|[]]; simpl; intros.
- reflexivity.
- rewrite app_assoc; etransitivity.
  apply Permutation_app_tail; etransitivity.
  apply Permutation_app_comm. apply Permutation_merge. apply IHstack.
- reflexivity.
Qed.

Theorem Permutation_merge_all stack :
  Permutation (flatten stack) (merge_all stack).
Proof.
induction stack as [|[]]; simpl. easy.
transitivity (l ++ merge_all stack).
apply Permutation_app_head, IHstack.
apply Permutation_merge. apply IHstack.
Qed.

Theorem Permutation_merge_iter l stack :
  Permutation (flatten stack ++ l) (merge_iter stack l).
Proof.
revert stack; induction l; simpl; intros.
rewrite app_nil_r; apply Permutation_merge_all.
rewrite cons_app, app_assoc; etransitivity.
apply Permutation_app_tail; etransitivity.
apply Permutation_app_comm.
apply Permutation_merge_push.
apply IHl.
Qed.

Theorem Permutation_merge_sort l :
  Permutation l (merge_sort l).
Proof.
apply (Permutation_merge_iter l []).
Qed.

End Permutation.

End Merge_sort.
