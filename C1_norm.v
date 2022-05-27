(* Produce canonical lists using merge sort and deduplication. *)

Require Import Permutation.
From larith Require Import A_setup B1_utils.

Notation Sorted leb := (RTC (λ x y, leb x y = true)).
Notation Increasing leb := (RTC (λ x y, leb y x = false)).

(*
The primary goal of this file is to supply an efficient algorithm to normalize
lists of states in the powerset automaton construction. For the correctness of
the depth-first search, a list containing all states must exist. To realize this
we will represent states as strictly increasing lists.
*)
Section Canonical_lists.

Variable X : Type.
Variable leb : X -> X -> bool.

Notation Sorted := (Sorted leb).
Notation Increasing := (Increasing leb).

Notation "x <= y" := (leb x y = true) (at level 70).
Notation "x > y" := (leb x y = false) (at level 70).

(* Proving `Sorted (mergesort l)` only requires totality. *)
Hypothesis leb_total : ∀x y, x <= y \/ y <= x.

(* Proving `Increasing (dedup l)` only requires anti-symmetry. *)
Hypothesis leb_asym : ∀x y, x <= y /\ y <= x <-> x = y.

(* Proving uniqueness of increasing lists uses the above + transitivity. *)
Hypothesis leb_trans : ∀x y z, x <= y -> y <= z -> x <= z.

(* These three hypotheses represent a linear order. *)
Definition Linear_order :=
  (∀x y, x <= y /\ y <= x <-> x = y) /\
  (∀x y z, x <= y -> y <= z -> x <= z) /\
  (∀x y, x <= y \/ y <= x).

Local Lemma gt_leb x y :
  x > y -> y <= x.
Proof.
destruct (leb_total y x); [easy|congruence].
Qed.

Local Lemma leb_refl x :
  x <= x.
Proof.
apply leb_asym; easy.
Qed.

(******************************************************************************)
(* I. A merge sort algorithm.                                                 *)
(******************************************************************************)
(* Initial author: Hugo Herbelin, Oct 2009                                    *)
(* This section only relies on the leb_total hypothesis.                      *)
(******************************************************************************)
Section Mergesort.

Notation Sorted_stack stack := (Forall Sorted (strip stack)).
Notation flatten stack := (concat (strip stack)).

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

Section Sorted.

Theorem Sorted_merge l1 l2 :
  Sorted l1 -> Sorted l2 -> Sorted (merge l1 l2).
Proof.
revert l2; induction l1; induction l2; intros; simpl; auto.
destruct (leb a a0) eqn:Heq1.
- inv H. simpl; apply RTC_cons; easy.
  assert(IH := IHl1 _ H3 H0); simpl; simpl in IH.
  destruct (leb y a0); apply RTC_cons; easy.
- apply gt_leb in Heq1.
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

(******************************************************************************)
(* II. Deduplication of sorted lists.                                         *)
(******************************************************************************)
(* This section only relies on the leb_asym hypothesis.                       *)
(******************************************************************************)
Section Deduplication.

Fixpoint dedup l :=
  match l with
  | [] => []
  | x :: l' =>
    match l' with
    | []     => [x]
    | y :: _ => if leb y x then dedup l' else x :: dedup l'
    end
  end.

Theorem dedup_eqv l x :
  Sorted l -> In x (dedup l) <-> In x l.
Proof.
intros; induction l; simpl.
easy. destruct l. easy. inv H.
apply IHl in H2; destruct (leb x0 a) eqn:Ha.
- assert(a = x0) by (apply leb_asym; easy); subst.
  etransitivity. apply H2. simpl; intuition.
- symmetry; transitivity (a = x \/ In x (dedup (x0 :: l))).
  rewrite H2; reflexivity. easy.
Qed.

Lemma Increasing_cons_dedup x y l :
  Sorted (y :: l) -> y > x -> Increasing (x :: dedup (y :: l)).
Proof.
revert x y; induction l; intros. repeat constructor; easy.
replace (dedup _) with (if leb a y then dedup (a::l) else y :: dedup (a::l))
by easy; inv H; destruct (leb a y) eqn:Ha.
- apply IHl. easy. assert(a = y) by (now apply leb_asym); subst; easy.
- constructor. apply IHl. all: easy.
Qed.

Theorem Increasing_dedup l :
  Sorted l -> Increasing (dedup l).
Proof.
induction l; simpl; intros. constructor.
inv H. constructor. destruct (leb y a) eqn:Hy.
auto. apply Increasing_cons_dedup; easy.
Qed.

Theorem length_dedup l :
  (length (dedup l) <= length l)%nat.
Proof.
induction l. easy. destruct l. easy.
replace (dedup _) with (if leb x a then dedup (x::l) else a :: dedup (x::l))
by easy; destruct (leb _). apply le_S, IHl. apply le_n_S, IHl.
Qed.

End Deduplication.

(******************************************************************************)
(* III. Uniqueness of increasing lists.                                       *)
(******************************************************************************)
Section Uniqueness.

Lemma Increasing_le x y l :
  Increasing (y :: l) -> x <= y -> ¬In x l.
Proof.
revert y; induction l; simpl; intros. easy.
inv H; intros []. subst; congruence.
apply IHl with (y:=a); try easy.
apply leb_trans with (y:=y). easy. apply gt_leb, H5.
Qed.

Corollary Increasing_tl x l :
  Increasing (x :: l) -> ¬In x l.
Proof.
intros; apply Increasing_le with (y:=x).
apply H. apply leb_refl.
Qed.

Corollary Increasing_lt x y l :
  Increasing (y :: l) -> y > x -> ¬In x (y :: l).
Proof.
intros Hy Hx [F|F].
subst; rewrite leb_refl in Hx; easy.
apply Increasing_le with (y:=y) in F.
easy. easy. apply gt_leb, Hx.
Qed.

Theorem Increasing_unique l1 l2 :
  (∀x, In x l1 <-> In x l2) ->
  Increasing l1 -> Increasing l2 ->
  l1 = l2.
Proof.
revert l2; induction l1; destruct l2; intros. easy.
1,2: exfalso; eapply in_nil, H, in_eq. assert(a = x). 
- apply leb_asym; split.
  + destruct (leb a x) eqn:F; [easy|exfalso].
    eapply Increasing_lt; [apply H0|apply F|apply H, in_eq].
  + destruct (leb x a) eqn:F; [easy|exfalso].
    eapply Increasing_lt; [apply H1|apply F|apply H, in_eq].  
- subst; apply wd, IHl1. apply Increasing_tl in H0, H1.
  intros y; split; intros Y; eapply in_cons in Y as Z; apply H in Z; inv Z.
  all: eapply RTC_weaken. apply H0. apply H1.
Qed.

End Uniqueness.

(******************************************************************************)
(* IV. The normalization function.                                            *)
(******************************************************************************)
Section Normalization.

Definition normalize l := dedup (mergesort l).

Theorem Increasing_normalize l :
  Increasing (normalize l).
Proof.
apply Increasing_dedup, Sorted_mergesort.
Qed.

Theorem normalize_eqv l x :
  In x (normalize l) <-> In x l.
Proof.
etransitivity. apply dedup_eqv, Sorted_mergesort.
split; apply Permutation_in. apply Permutation_sym.
all: apply Permutation_mergesort.
Qed.

Theorem normalize_fixed_point l :
  Increasing l -> normalize l = l.
Proof.
intros; apply Increasing_unique. apply normalize_eqv.
apply Increasing_normalize. apply H.
Qed.

End Normalization.

(******************************************************************************)
(* V. Exhausting all increasing sequences over a finite domain.               *)
(******************************************************************************)
Section Powerset.

Notation Below x := (Forall (λ y, leb y x = false)).

Fixpoint powerset (dom : list X) :=
  match dom with
  | [] => [[]]
  | a :: dom' => let p := powerset dom' in p ++ map (cons a) p
  end.

Theorem Increasing_Below x l :
  Increasing (x :: l) -> Below x l.
Proof.
intros; apply Forall_forall; intros.
destruct (leb x0 x) eqn:Hx; [|easy].
apply Increasing_le with (l:=l) in Hx; easy.
Qed.

Theorem Below_Increasing x l :
  Increasing l -> Below x l -> Increasing (x :: l).
Proof.
destruct l; intros; constructor.
easy. inv H0.
Qed.

Local Lemma X_dec (x y : X) :
  {x = y} + {x ≠ y}.
Proof.
destruct (leb x y) eqn:Hx, (leb y x) eqn:Hy. left; apply leb_asym; easy.
all: right; intros F; apply leb_asym in F; rewrite Hx, Hy in F; easy.
Qed.

Local Lemma Increasing_remove x l :
  Increasing l -> Increasing (remove X_dec x l).
Proof.
induction l; simpl; intros. constructor.
apply RTC_weaken in H as Hl; apply IHl in Hl.
destruct (X_dec x a); [easy|].
apply Below_Increasing; [easy|].
apply Forall_incl with (l':=l); intros.
apply in_remove in H0; easy. apply Increasing_Below, H.
Qed.

Theorem Increasing_In_powerset dom l :
  (∀x, In x l -> In x dom) ->
  Increasing dom -> Increasing l ->
  In l (powerset dom).
Proof.
revert l; induction dom as [|e dom']; simpl; intros.
destruct l; [now left|right]; eapply H, in_eq.
assert(He := Increasing_remove e _ H1).
assert(In (remove X_dec e l) (powerset dom')). {
  apply IHdom'. intros x Hx; apply in_remove in Hx as [].
  apply H in H2 as []; [congruence|easy].
  eapply RTC_weaken, H0. easy. }
apply in_app_iff; destruct (in_dec X_dec e l).
2: left; rewrite notin_remove in H2; easy. right.
apply in_map_iff; exists (remove X_dec e l); split; [|easy].
apply Increasing_unique; try easy.
- split. intros []. subst; easy. apply in_remove in H3; easy.
  intros; destruct (X_dec x e). subst; apply in_eq.
  apply in_cons, in_in_remove; easy.
- apply Below_Increasing.
  apply Increasing_remove, H1.
  apply Forall_incl with (l':=dom'); intros.
  apply in_remove in H3 as [].
  apply H in H3 as []; [congruence|easy].
  apply Increasing_Below, H0.
Qed.

End Powerset.

End Canonical_lists.

Arguments Linear_order {_}.
Arguments mergesort {_}.
Arguments dedup {_}.
Arguments normalize {_}.
Arguments powerset {_}.
