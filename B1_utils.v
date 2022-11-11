(* Theorems about basic logic and lists. *)

Require Import PeanoNat.
From larith Require Import A_setup.

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
(* II. Lists witnessing a transitive path.                                    *)
(******************************************************************************)
Section Reflexive_transitive_closure.

Variable X : Type.
Variable R : X -> X -> Prop.

Inductive RTC : list X -> Prop :=
  | RTC_nil : RTC []
  | RTC_refl x : RTC [x]
  | RTC_cons x y l : RTC (y :: l) -> R x y -> RTC (x :: y :: l).

Theorem RTC_weaken x l :
  RTC (x :: l) -> RTC l.
Proof.
destruct l; intros.
constructor. inv H.
Qed.

Theorem RTC_trans l1 l2 d :
  RTC l1 -> RTC (last l1 d :: l2) -> RTC (l1 ++ l2).
Proof.
induction l1; simpl; intros. inv H0.
destruct l1; subst; simpl in *. easy.
inv H; apply RTC_cons. apply IHl1; easy. easy.
Qed.

Theorem RTC_app_inv l1 l2 :
  RTC (l1 ++ l2) -> RTC l1 /\ RTC l2.
Proof.
induction l1; simpl; intros.
split; [apply RTC_nil|easy]. inv H.
- apply eq_sym, app_eq_nil in H2 as [H1 H2]; subst.
  split; [apply RTC_refl|apply RTC_nil].
- rewrite H1 in H2; apply IHl1 in H2. split; [|easy].
  destruct l1; [apply RTC_refl|inv H1; apply RTC_cons; easy].
Qed.

End Reflexive_transitive_closure.

Arguments RTC {_}.

(******************************************************************************)
(* III. Various list utilities.                                               *)
(******************************************************************************)
Module ListUtils.

Theorem cons_app {X} (x : X) l :
  x :: l = [x] ++ l.
Proof.
easy.
Qed.

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

Theorem split_list {X} (x : X) l :
  In x l -> ∃l1 l2, l = l1 ++ x :: l2.
Proof.
induction l; intros. easy. inv H.
- exists [], l; easy.
- apply IHl in H0 as [l1 [l2 H]].
  exists (a :: l1), l2; simpl; rewrite H; easy.
Qed.

Theorem Forall_incl {X} P (l l' : list X) :
  (∀x, In x l -> In x l') -> Forall P l' -> Forall P l.
Proof.
intros; apply Forall_forall; intros.
apply Forall_forall with (x:=x) in H0; auto.
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

Theorem split_at_last_instance (x : X) l :
  In x l -> ∃l1 l2, l = l1 ++ x :: l2 /\ ¬In x l2.
Proof.
induction l; intros. easy. inv H.
destruct (in_dec dec x l) as [H0|H0].
1,3: apply IHl in H0 as [l1 [l2 []]]; rewrite H.
1: exists (x :: l1), l2. 2: exists (a :: l1), l2. 3: exists [], l. all: easy.
Qed.

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

Section Definition_using_pfilter.

Variable l s : list X.

Definition intersect :=
  pfilter (λ x, In x s) (λ x, in_dec dec x s) l.

Definition subtract :=
  pfilter (λ x, ¬In x s) (λ x, not_dec _ (in_dec dec x s)) l. 

Corollary intersect_spec x :
  In x intersect <-> In x l /\ In x s.
Proof.
apply pfilter_spec.
Qed.

Corollary subtract_spec x :
  In x subtract <-> In x l /\ ¬In x s.
Proof.
apply pfilter_spec.
Qed.

Theorem subtract_length :
  length subtract = length l - length intersect.
Proof.
unfold subtract, intersect; induction l; simpl pfilter. easy.
destruct (in_dec _), (not_dec _ _); try easy.
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

End Definition_using_pfilter.

Theorem subtract_length_le_cons_r x a b :
  length (subtract a (x :: b)) <= length (subtract a b).
Proof.
induction a; simpl. easy.
destruct (dec _), (in_dec _); simpl.
2: apply le_S. 4: apply le_n_S. all: apply IHa.
Qed.

Theorem length_subtract_le_incl_r a b c :
  (∀x, In x b -> In x c) ->
  length (subtract a c) <= length (subtract a b).
Proof.
induction a; simpl; intros. easy.
destruct (in_dec _), (in_dec _); simpl.
2: apply le_S. 4: apply le_n_S.
3: exfalso; apply n, H, i. all: apply IHa, H.
Qed.

Theorem subtract_length_lt_cons_r x a b :
  In x a -> ¬In x b ->
  length (subtract a (x :: b)) < length (subtract a b).
Proof.
induction a; simpl; intros. easy.
destruct H, (dec _), (in_dec _); subst; simpl; try easy.
apply Nat.lt_succ_r, subtract_length_le_cons_r.
1: apply Nat.lt_lt_succ_r. 3: apply Nat.lt_succ_r.
all: apply IHa; easy.
Qed.

End Intersection_and_subtraction.

End List_constructions_using_decidability.

Arguments map2 {_ _ _}.
Arguments strip {_}.
Arguments pfilter {_}.
Arguments intersect {_}.
Arguments subtract {_}.

End ListUtils.
Export ListUtils.
