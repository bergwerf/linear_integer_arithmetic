(* Basic utilities for various purposes. *)

Require Import Utf8 Nat PeanoNat List Lia.
From larith Require Import tactics notations.
Import ListNotations.

(******************************************************************************)
(* I. Laws of constructive propositional and predicate logic.                 *)
(******************************************************************************)
Section Laws_of_logic.

Section Propositions.

Variable P Q : Prop.

Theorem triple_not :
  ¬¬¬P -> ¬P.
Proof.
auto.
Qed.

Theorem weaken :
  P -> ¬¬P.
Proof.
auto.
Qed.

Theorem contra :
  (P -> Q) -> (¬Q -> ¬P).
Proof.
auto.
Qed.

Theorem not_or_and :
  ¬(P \/ Q) <-> ¬P /\ ¬Q.
Proof.
split; auto. now intros [H1 H2] [H|H].
Qed.

Theorem and_remove_r :
  Q -> P /\ Q <-> P.
Proof.
easy.
Qed.

Theorem or_remove_r :
  ¬Q -> P \/ Q <-> P.
Proof.
intros nQ; split; intros.
now destruct H. now left.
Qed.

Theorem exfalso_iff :
  ¬P -> ¬Q -> P <-> Q.
Proof.
easy.
Qed.

Variable P_dec : {P} + {¬P}.
Variable Q_dec : {Q} + {¬Q}.

Theorem not_dec :
  {¬P} + {¬¬P}.
Proof.
destruct P_dec; auto.
Qed.

Theorem and_dec :
  {P /\ Q} + {¬(P /\ Q)}.
Proof.
destruct P_dec, Q_dec.
now left. all: now right.
Qed.

End Propositions.

Section Predicates.

Variable X Y : Type.
Variable P Q : X -> Prop.
Variable R : X -> Y -> Prop.

Theorem ex_iff :
  (∀x, P x <-> Q x) -> (∃x, P x) <-> (∃x, Q x).
Proof.
intros H; split; intros [x Hx]; exists x; apply H, Hx.
Qed.

Theorem sigma_function :
  (∀x, Σ y, R x y) -> Σ f : X -> Y, ∀x, R x (f x).
Proof.
intros H; exists (λ x, projT1 (H x)).
intros; destruct (H x); easy.
Qed.

End Predicates.

End Laws_of_logic.

(******************************************************************************)
(* II. Various list utilities.                                                *)
(******************************************************************************)
Module ListUtils.

Theorem list_prod_nil_r {X Y} (l : list X) :
  @list_prod X Y l nil = nil.
Proof.
now induction l.
Qed.

Theorem list_prod_single {X Y} (x : X) (y : Y) :
  [(x, y)] = list_prod [x] [y].
Proof.
easy.
Qed.

Theorem list_singleton {X} (l : list X) :
  length l = 1 -> ∃x, l = [x].
Proof.
intros. destruct l. easy. destruct l.
now exists x. easy.
Qed.

Notation lmax l := (fold_right max 0 l).

Section Maximum.

Lemma lmax_app l l' :
  lmax (l ++ l') = max (lmax l) (lmax l').
Proof.
induction l; simpl. easy.
rewrite IHl; lia.
Qed.

Lemma lmax_in n l :
  In n l -> n <= lmax l.
Proof.
induction l; simpl. easy.
intros [H|H]. subst. lia.
apply IHl in H. lia.
Qed.

End Maximum.

Section Forall2.

Section Type_agnostic.

Variable X Y Z : Type.
Variable R S : X -> Y -> Prop.

Theorem Forall2_eq (l l' : list X) :
  Forall2 eq l l' <-> l = l'.
Proof.
revert l'; induction l; destruct l'; try easy.
split; intros H; inv H. apply IHl in H5; now subst.
apply Forall2_cons, IHl; easy.
Qed.

Theorem Forall2_impl xs ys :
  Forall2 R xs ys -> (∀x y, R x y -> S x y) -> Forall2 S xs ys.
Proof.
intros HR HRS; induction HR. apply Forall2_nil.
apply Forall2_cons. apply HRS, H. apply IHHR.
Qed.

Theorem Forall2_map (f : Z -> Y) xs zs :
  Forall2 R xs (map f zs) <-> Forall2 (λ x z, R x (f z)) xs zs.
Proof.
revert zs; induction xs; destruct zs; simpl; intros; try easy.
split; intros H; inv H. all: apply Forall2_cons; [easy|now apply IHxs].
Qed.

End Type_agnostic.

Corollary Forall2_In_singleton {X} (l l' : list X) :
  Forall2 (@In _) l (map (λ x, [x]) l') <-> l = l'.
Proof.
rewrite Forall2_map, <-Forall2_eq. split; intros.
all: eapply Forall2_impl; [apply H|].
all: intros; simpl in *. inv H0. now left.
Qed.

End Forall2.

Section Mapping.

Variable X Y : Type.
Variable f : X -> Y.

Theorem map_map_singleton xs :
  map (λ x, [f x]) xs = map (λ y, [y]) (map f xs).
Proof.
now rewrite map_map.
Qed.

Theorem nth_map i l d x :
  nth i l d = x -> nth i (map f l) (f d) = f x.
Proof.
revert i; induction l; destruct i; simpl.
1-3: congruence. apply IHl.
Qed.

Hypothesis f_inj : ∀x x', f x = f x' -> x = x'.

Theorem nth_map_inj i l d x :
  nth i (map f l) (f d) = f x -> nth i l d = x.
Proof.
revert i; induction l; destruct i; simpl.
1-3: apply f_inj. apply IHl.
Qed.

End Mapping.

Section Double_mapping.

Variable X Y Z : Type.
Variable f : X -> Y -> Z.

Fixpoint map2 xs ys :=
  match xs, ys with
  | x :: xs', y :: ys' => f x y :: map2 xs' ys'
  | _, _ => []
  end.

End Double_mapping.

Arguments map2 {_ _ _}.

Section Trimming.

Variable X : Type.
Variable default : X.

Fixpoint trim n (l : list X) :=
  match n with
  | 0   => []
  | S m =>
    match l with
    | [] => default :: trim m []
    | x :: l' =>  x :: trim m l'
    end
  end.

End Trimming.

Arguments trim {_}.

Section Strip_option_list.

Variable X : Type.

Fixpoint strip (l : list (option X)) :=
  match l with
  | [] => []
  | None :: l' => strip l'
  | Some x :: l' => x :: strip l'
  end.

Theorem strip_map_id l :
  strip (map Some l) = l.
Proof.
induction l; simpl.
easy. now rewrite IHl.
Qed.

Theorem strip_app l l' :
  strip (l ++ l') = strip l ++ strip l'.
Proof.
induction l as [|[x|] l]; simpl. easy.
now rewrite IHl. apply IHl.
Qed.

End Strip_option_list.

Arguments strip {_}.

Section List_constructions_using_decidability.

Variable X : Type.
Hypothesis dec : ∀x y : X, {x = y} + {x ≠ y}.

Section Powerset.

Fixpoint powerset (l : list X) :=
  match l with
  | []      => [[]]
  | x :: l' => let p := powerset l' in p ++ map (cons x) p
  end.

Theorem powerset_length l :
  length (powerset l) = 2^length l.
Proof.
induction l; simpl. easy.
now rewrite Nat.add_0_r, app_length, map_length, ?IHl.
Qed.

Theorem powerset_spec l s x :
  In s (powerset l) -> In x s -> In x l.
Proof.
revert s; induction l; simpl; intros.
- destruct H; subst; easy.
- destruct (dec a x). now left. right.
  apply in_app_or in H as [H|H]. now apply IHl in H.
  apply in_map_iff in H as [s' [R H]]; subst.
  inv H0. now apply IHl in H.
Qed.

Theorem powerset_lookup l s :
  (∀x, In x s -> In x l) ->
  Σ t, In t (powerset l) /\ ∀x, In x s <-> In x t.
Proof.
revert s; induction l; simpl; intros.
- exists []; split. now left. split; [apply H|easy].
- pose(s' := remove dec a s).
  destruct (IHl s') as [t [H1t H2t]].
  + unfold s'; intros. apply in_remove in H0 as [H1 H2].
    apply H in H1 as [H1|H1]. congruence. easy.
  + exists (if in_dec dec a s then a :: t else t); split.
    * destruct (in_dec dec a s); apply in_app_iff; [right|left].
      apply in_map_iff; now exists t. easy.
    * intros; destruct (in_dec dec a s); simpl; rewrite <-H2t.
      destruct (dec x a); subst; split; intros H'; try destruct H'; auto.
      right; now apply in_in_remove. congruence. now apply in_remove in H0.
      unfold s'; rewrite notin_remove; easy.
Qed.

End Powerset.


Section Filtering.

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

End Filtering.

Section Intersection_and_subtraction.

Variable l l' : list X.

Definition intersect :=
  pfilter (λ x, In x l') (λ x, in_dec dec x l') l.

Definition subtract :=
  pfilter (λ x, ¬In x l') (λ x, not_dec _ (in_dec dec x l')) l. 

Corollary intersect_spec x :
  In x intersect <-> In x l /\ In x l'.
Proof.
apply pfilter_spec.
Qed.

Corollary subtract_spec x :
  In x subtract <-> In x l /\ ¬In x l'.
Proof.
apply pfilter_spec.
Qed.

Theorem subtract_length :
  length subtract = length l - length intersect.
Proof.
unfold subtract, intersect; induction l; simpl pfilter. easy.
destruct (in_dec dec a l'), (not_dec _ _); try easy.
simpl length; rewrite IHl0; clear IHl0. remember (pfilter _ _ l0) as l1.
assert(length l1 <= length l0) by (subst; apply pfilter_length). lia.
Qed.

Corollary intersect_length :
  length intersect = length l - length subtract.
Proof.
rewrite subtract_length.
assert(length intersect <= length l) by apply pfilter_length. lia.
Qed.

End Intersection_and_subtraction.

End List_constructions_using_decidability.

Arguments powerset {_}.
Arguments pfilter {_}.
Arguments intersect {_}.
Arguments subtract {_}.

End ListUtils.
Export ListUtils.
