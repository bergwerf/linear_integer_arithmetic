(* Basic utilities for various purposes. *)

Require Import Utf8 PeanoNat List.
From larith Require Import tactics notations.
Import ListNotations.

(******************************************************************************)
(* I. Laws of constructive propositional and predicate logic.                 *)
(******************************************************************************)
Section Laws_of_logic.

Section Propositions.

Variable P Q : Prop.

Theorem contra :
  (P -> Q) -> (¬Q -> ¬P).
Proof.
auto.
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
Defined.

End Propositions.

Section Predicates.

Variable X Y : Type.
Variable P Q : X -> Prop.

Theorem ex_iff :
  (∀x, P x <-> Q x) -> (∃x, P x) <-> (∃x, Q x).
Proof.
intros H; split; intros [x Hx]; exists x; apply H, Hx.
Qed.

End Predicates.

End Laws_of_logic.

(******************************************************************************)
(* II. Various list utilities.                                                *)
(******************************************************************************)
Module ListUtils.

Theorem list_singleton {X} (l : list X) :
  length l = 1 -> ∃x, l = [x].
Proof.
intros. destruct l. easy. destruct l.
now exists x. easy.
Qed.

Theorem last_cons {X} (x d : X) l :
  last (x :: l) d = last l x.
Proof.
revert x d; induction l; simpl; intros.
easy. destruct l. easy. apply IHl.
Qed.

Theorem last_app {X} (x d : X) l1 l2 :
  last (l1 ++ x :: l2) d = last l2 x.
Proof.
revert d; induction l1; intros.
rewrite app_nil_l; apply last_cons.
rewrite <-app_comm_cons, last_cons; apply IHl1.
Qed.

Notation lmax l := (fold_right max 0 l).

Theorem lmax_in n l :
  In n l -> n <= lmax l.
Proof.
induction l; simpl. easy.
intros [H|H]; subst. apply Nat.le_max_l.
apply Nat.max_le_iff; right; apply IHl, H.
Qed.

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

Theorem map_map_singleton l :
  map (λ x, [f x]) l = map (λ y, [y]) (map f l).
Proof.
now rewrite map_map.
Qed.

Theorem flat_map_singleton l :
  flat_map (λ x, [f x]) l = map f l.
Proof.
induction l; simpl.
easy. now rewrite IHl.
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

Section List_constructions_using_decidability.

Variable X : Type.
Hypothesis dec : ∀x y : X, {x = y} + {x ≠ y}.

Theorem split_list (x : X) l :
  Σ l1 l2, x :: l = l1 ++ x :: l2 /\ ¬In x l2.
Proof.
induction l. exists [], []; easy.
destruct IHl as [l1 [l2 [H1 H2]]], (dec a x); subst.
- rewrite H1. exists (x :: l1), l2; easy.
- destruct l1; simpl in H1; inv H1.
  exists [], (a :: l2); simpl; split; [easy|intros []; easy].
  exists (x0 :: a :: l1), l2; easy.
Qed.

Section Powerset.

Fixpoint powerset (u : list X) :=
  match u with
  | [] => [[]]
  | a :: v => let p := powerset v in p ++ map (cons a) p
  end.

Fixpoint normalize (u l : list X) :=
  match u with
  | [] => []
  | a :: v =>
    let tl := normalize v (remove dec a l) in
    if in_dec dec a l then a :: tl else tl
  end.

Theorem powerset_length u :
  length (powerset u) = 2^length u.
Proof.
induction u; simpl. easy.
now rewrite Nat.add_0_r, app_length, map_length, ?IHu.
Qed.

Theorem normalize_spec u l :
  In (normalize u l) (powerset u).
Proof.
revert l; induction u; simpl; intros. now left.
destruct (in_dec dec a l); apply in_app_iff; [right|left].
apply in_map. all: apply IHu.
Qed.

Theorem normalize_sound u l x :
  In x (normalize u l) -> In x l.
Proof.
revert l; induction u; simpl; intros. easy.
destruct (in_dec dec a l); simpl. inv H; rename H0 into H.
all: apply IHu, in_remove in H; easy.
Qed.

Theorem normalize_complete u l x :
  In x u -> In x l -> In x (normalize u l).
Proof.
revert l; induction u; simpl; intros. easy.
destruct (in_dec dec a l), (dec x a), H; simpl; subst; auto; try easy. right.
all: apply IHu; [easy|]; apply in_in_remove; easy.
Qed.

Theorem normalize_normalize u l :
  normalize u (normalize u l) = normalize u l.
Proof.
revert l; induction u; simpl; intros. easy.
destruct (in_dec dec a l); simpl.
destruct (dec a a); [|easy]. apply wd.
2: destruct (in_dec _ _ _).
2: apply normalize_sound, remove_In in i; easy.
all: rewrite notin_remove; [apply IHu|].
all: eapply contra; [apply normalize_sound|apply remove_In].
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
destruct (P_dec a); simpl.
apply le_n_S, IHl. apply le_S, IHl.
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
assert(length l1 <= length l0) by (subst; apply pfilter_length).
rewrite <-Nat.sub_succ_l. reflexivity. easy.
Qed.

Corollary intersect_length :
  length intersect = length l - length subtract.
Proof.
rewrite subtract_length.
assert(length intersect <= length l) by apply pfilter_length.
symmetry; apply Nat.add_sub_eq_l, Nat.sub_add, H.
Qed.

End Intersection_and_subtraction.

End List_constructions_using_decidability.

Arguments map2 {_ _ _}.
Arguments strip {_}.
Arguments powerset {_}.
Arguments normalize {_}.
Arguments pfilter {_}.
Arguments intersect {_}.
Arguments subtract {_}.

End ListUtils.
Export ListUtils.
