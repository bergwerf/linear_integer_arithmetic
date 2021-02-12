(* Algorithms for canonical lists, most notably a merge-sort function. *)

Require Import Utf8 List Permutation.
From larith Require Import tactics notations utilities.

Notation Sorted leb := (RTC (λ x y, leb x y = true)).

(*
The primary goal of this file is to supply an efficient algorithm to normalize
lists of states in the powerset automaton construction. For the correctness of
the depth-first search, a list containing all states must exist. To realize this
we will represent states as sorted lists without duplicated elements.
*)
Section Canonical_lists.

Variable X : Type.
Variable leb : X -> X -> bool.

Notation Sorted := (Sorted leb).
Notation "x <= y" := (leb x y = true) (at level 70).
Notation "x > y" := (leb x y = false) (at level 70).

(* This is the only hypothesis needed to prove mergesort correct. *)
Hypothesis leb_total : ∀x y, x <= y \/ y <= x.

(* A merge-sort algorithm. *)
(* Initial author: Hugo Herbelin, Oct 2009 *)
(* Altered to the style of this repository. *)
Section Mergesort.

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

Definition mergesort := merge_iter [].

(** The proof of correctness *)

Notation Sorted_stack stack := (Forall Sorted (strip stack)).
Notation flatten stack := (concat (strip stack)).

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

Theorem Sorted_mergesort l :
  Sorted (mergesort l).
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

Theorem Permutation_mergesort l :
  Permutation l (mergesort l).
Proof.
apply (Permutation_merge_iter l []).
Qed.

End Permutation.

End Mergesort.

(*
To prove that a sorted list without duplicated elements is unique, we need that
leb is transitive and anti-symmetric. We can also prove the correctness of an
efficient deduplication function for sorted lists using these hypotheses.
*)
Hypothesis leb_trans : ∀x y z, x <= y -> y <= z -> x <= z.
Hypothesis leb_asym : ∀x y, x <= y /\ y <= x <-> x = y.

Local Lemma leb_refl x :
  x <= x.
Proof.
apply leb_asym; easy.
Qed.

Lemma Sorted_lt_hd x y l :
  Sorted (y :: l) -> y > x -> ¬In x (y :: l).
Proof.
revert y; induction l; simpl; intros.
- intros []; [subst|easy]. now rewrite leb_refl in H0.
- inv H; intros []. subst; now rewrite leb_refl in H0.
  apply IHl in H. easy. easy.
  destruct (leb a x) eqn:Ha; [|easy].
  rewrite leb_trans with (y:=a) in H0; easy.
Qed.

Theorem Sorted_NoDup_unique l1 l2 :
  (∀x, In x l1 <-> In x l2) ->
  Sorted l1 -> Sorted l2 ->
  NoDup l1 -> NoDup l2 ->
  l1 = l2.
Proof.
revert l2; induction l1; destruct l2; intros. easy.
1,2: exfalso; eapply in_nil, H, in_eq. assert(a = x).
- (* Prove a = x using leb_asym. *)
  apply leb_asym; split.
  + destruct (leb a x) eqn:F; [easy|exfalso].
    eapply Sorted_lt_hd. apply H0. apply F. apply H, in_eq.
  + destruct (leb x a) eqn:F; [easy|exfalso].
    eapply Sorted_lt_hd. apply H1. apply F. apply H, in_eq.
- (* Prove l1 = l2 using IHl. *)
  apply RTC_weaken in H0, H1; inv H2; inv H3. apply wd, IHl1; try easy.
  split; intros; eapply in_cons in H2 as H3; apply H in H3; inv H3.
Qed.

Section Deduplication.

Fixpoint dedup l :=
  match l with
  | [] => []
  | x :: l' =>
    match l' with
    | [] => [x]
    | y :: l'' => if leb y x then dedup l' else x :: dedup l'
    end
  end.

Theorem dedup_eqv l x :
  Sorted l -> In x (dedup l) <-> In x l.
Proof.
intros Hsorted; induction l; simpl.
easy. destruct l. easy. inv Hsorted.
apply IHl in H1; destruct (leb x0 a) eqn:Ha.
- assert(a = x0) by (apply leb_asym; easy); subst.
  etransitivity. apply H1. simpl; intuition.
- symmetry; transitivity (a = x \/ In x (dedup (x0 :: l))).
  rewrite H1; reflexivity. easy.
Qed.

Lemma Sorted_cons_dedup x y l :
  Sorted (y :: l) -> x <= y -> Sorted (x :: dedup (y :: l)).
Proof.
revert x y; induction l; intros. constructor; easy.
replace (dedup _) with (if leb a y then dedup (a::l) else y :: dedup (a::l))
by easy; inv H. destruct (leb a y) eqn:Ha.
- apply IHl. easy. apply leb_trans with (y:=y); easy.
- constructor. apply IHl. all: easy.
Qed.

Theorem Sorted_dedup l :
  Sorted l -> Sorted (dedup l).
Proof.
induction l; simpl; intros. easy.
inv H. constructor. destruct (leb y a). auto.
apply Sorted_cons_dedup; easy.
Qed.

Theorem NoDup_dedup l :
  Sorted l -> NoDup (dedup l).
Proof.
induction l; simpl; intros. constructor.
inv H. constructor; [easy|constructor].
apply IHl in H2 as IH; destruct (leb y a) eqn:H. easy.
constructor; [|easy]. intros F; apply dedup_eqv with (l:=y::_) in F.
apply Sorted_lt_hd in F; easy. easy.
Qed.

End Deduplication.

(* Deduplicated sorted lists are fixed points of dedup ∘ mergesort. *)
Theorem dedup_mergesort_fixed_point l :
  Sorted l -> NoDup l -> dedup (mergesort l) = l.
Proof.
intros; apply Sorted_NoDup_unique; try easy.
- intros; etransitivity. apply dedup_eqv, Sorted_mergesort.
  split; apply Permutation_in. apply Permutation_sym.
  all: apply Permutation_mergesort.
- apply Sorted_dedup, Sorted_mergesort.
- apply NoDup_dedup, Sorted_mergesort.
Qed.

End Canonical_lists.
