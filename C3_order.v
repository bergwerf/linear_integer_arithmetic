(* Ordering using a comparison function. *)

From larith Require Import A_setup B1_utils C1_sort.

Record Order {X} (cmp : X -> X -> comparison) := Order_spec {
  cmp_eq : ∀x y, cmp x y = Eq <-> x = y;
  cmp_opp : ∀x y, cmp x y = CompOpp (cmp y x);
  cmp_lt_trans : ∀x y z, cmp x y = Lt -> cmp y z = Lt -> cmp x z = Lt;
}.

Arguments cmp_eq {_ _}.
Arguments cmp_opp {_ _}.
Arguments cmp_lt_trans {_ _}.

Theorem cmp_swap {X cmp} (ord : Order cmp) c (x y : X) :
  cmp x y = c <-> cmp y x = CompOpp c.
Proof.
rewrite (cmp_opp ord).
apply CompOpp_iff.
Qed.

Theorem cmp_trans {X cmp} (ord : Order cmp) c (x y z : X) :
  cmp x y = c -> cmp y z = c -> cmp x z = c.
Proof.
destruct c; intros.
- apply (cmp_eq ord) in H, H0; subst; apply (cmp_eq ord); reflexivity.
- apply (cmp_lt_trans ord) with (y:=y); easy.
- apply (cmp_swap ord); apply (cmp_swap ord) in H, H0; simpl in *.
  apply (cmp_lt_trans ord) with (y:=y); easy.
Qed.

Theorem cmp_dec {X} (cmp : X -> X -> comparison) :
  Order cmp -> ∀x y : X, {x = y} + {x ≠ y}.
Proof.
intros [cmp_eq _ _] x y.
destruct (cmp x y) eqn:H. left; apply cmp_eq, H.
all: right; intros F; apply cmp_eq in F; congruence.
Qed.

(******************************************************************************)
(* I. Ordering unit and bool.                                                 *)
(******************************************************************************)
Section Order_unit_and_bool.

Definition cmp_unit (x y : unit) := Eq.
Definition cmp_bool (x y : bool) :=
  match x, y with
  | true, true   => Eq
  | true, false  => Gt
  | false, true  => Lt
  | false, false => Eq
  end.

Theorem Order_unit :
  Order cmp_unit.
Proof.
Admitted.

Theorem Order_bool :
  Order cmp_bool.
Proof.
Admitted.

End Order_unit_and_bool.

(******************************************************************************)
(* II. Ordering the option type (add an initial element).                     *)
(******************************************************************************)
Section Order_option.

Variable X : Type.
Variable cmp : X -> X -> comparison.
Variable ord : Order cmp.

Definition cmp_option x1 x2 :=
  match x1, x2 with
  | None, None         => Eq
  | None, Some _       => Lt
  | Some _, None       => Gt
  | Some x1', Some x2' => cmp x1' x2'
  end.

Theorem Order_option :
  Order cmp_option.
Proof.
Admitted.

End Order_option.

(******************************************************************************)
(* III. Lexicographic ordering of pairs.                                      *)
(******************************************************************************)
Section Order_pair.

Variable A B : Type.
Variable cmpA : A -> A -> comparison.
Variable cmpB : B -> B -> comparison.
Variable ordA : Order cmpA.
Variable ordB : Order cmpB.

Definition cmp_pair ab1 ab2 :=
  match ab1, ab2 with
  | (a1, b1), (a2, b2) =>
    match cmpA a1 a2 with
    | Eq => cmpB b1 b2
    | Lt => Lt
    | Gt => Gt
    end
  end.

Lemma cmp_pair_Lt a1 b1 a2 b2 :
  cmp_pair (a1, b1) (a2, b2) = Lt <->
  cmpA a1 a2 = Lt \/ cmpA a1 a2 = Eq /\ cmpB b1 b2 = Lt.
Proof.
unfold cmp_pair; simpl.
destruct (cmpA a1 a2), (cmpB b1 b2);
split; intros []; auto; easy.
Qed.

Theorem Order_pair :
  Order cmp_pair.
Proof.
unfold cmp_pair; split.
- intros [a1 b1] [a2 b2]; simpl; split.
  + destruct (cmpA a1 a2) eqn:Ha, (cmpB b1 b2) eqn:Hb; try easy.
    apply (cmp_eq ordA) in Ha; apply (cmp_eq ordB) in Hb; subst; reflexivity.
  + intros H; injection H; intros.
    apply (cmp_eq ordA) in H1; apply (cmp_eq ordB) in H0.
    rewrite H0, H1; reflexivity.
- intros [a1 b1] [a2 b2]; simpl.
  destruct (cmpA a1 a2) eqn:Ha, (cmpB b1 b2) eqn:Hb;
  rewrite (cmp_swap ordA) in Ha; rewrite (cmp_swap ordB) in Hb;
  rewrite Ha, Hb; reflexivity.
- intros [a1 b1] [a2 b2] [a3 b3]; simpl; intros.
  apply cmp_pair_Lt in H, H0; apply cmp_pair_Lt;
  destruct H as [|[]], H0 as [|[]].
  + left; apply (cmp_trans ordA) with (y:=a2); easy.
  + left; rewrite (cmp_eq ordA) in H0; subst; easy.
  + left; rewrite (cmp_eq ordA) in H; subst; easy.
  + right; split.
    now apply (cmp_trans ordA) with (y:=a2).
    now apply (cmp_trans ordB) with (y:=b2).
Qed.

End Order_pair.

(******************************************************************************)
(* IV. Lexicographic ordering of lists.                                       *)
(******************************************************************************)
Section Order_list.

Variable X : Type.
Variable cmp : X -> X -> comparison.
Variable ord : Order cmp.

Fixpoint cmp_list l1 l2 :=
  match l1, l2 with
  | [], []     => Eq
  | [], _ :: _ => Lt
  | _ :: _, [] => Gt
  | x1 :: l1', x2 :: l2' =>
    match cmp x1 x2 with
    | Eq => cmp_list l1' l2'
    | Lt => Lt
    | Gt => Gt
    end
  end.

Theorem Order_list :
  Order cmp_list.
Proof.
Admitted.

End Order_list.

(******************************************************************************)
(* V. Ordering types carrying a specification.                                *)
(******************************************************************************)
Section Order_sig.

Variable X : Type.
Variable P : X -> Prop.
Variable cmp : X -> X -> comparison.
Variable ord : Order cmp.
Hypothesis pir : ∀(x y : Σ z, P z), projT1 x = projT1 y -> x = y.

Theorem Order_sig :
  Order (λ x y : Σ z, P z, cmp (projT1 x) (projT1 y)).
Proof.
split.
- intros [] []; simpl. etransitivity.
  apply (cmp_eq ord). split; intros.
  apply pir; easy. inv H.
- intros [] []; simpl. apply (cmp_opp ord).
- intros [] [] []; simpl. apply (cmp_trans ord).
Qed.

End Order_sig.

(******************************************************************************)
(* VI. A boolean ordering function for sorting.                               *)
(******************************************************************************)
Section Linear_order_function.

Variable X : Type.
Variable cmp : X -> X -> comparison.
Variable ord : Order cmp.

Definition cmp_leb x y :=
  match cmp x y with
  | Lt => true
  | Eq => true
  | Gt => false
  end.

Theorem Linear_order_cmp_leb :
  Linear_order cmp_leb.
Proof.
split; [|split]; intros.
- (* Anti-symmetry *)
  symmetry; etransitivity. symmetry; apply (cmp_eq ord). split.
  + intros. apply (cmp_swap ord) in H as H'.
    unfold cmp_leb; rewrite H, H'; easy.
  + unfold cmp_leb; intros [].
    destruct (cmp x y) eqn:Hx. easy.
    all: apply (cmp_swap ord) in Hx; rewrite Hx in H0; easy.
- (* Transitivity *)
  unfold cmp_leb in *; destruct (cmp x y) eqn:Hx, (cmp y z) eqn:Hy; try easy.
  1,2: apply (cmp_eq ord x y) in Hx; subst; rewrite Hy; easy.
  apply (cmp_eq ord y z) in Hy; subst; rewrite Hx; easy.
  rewrite (cmp_lt_trans ord x y z); easy.
- (* Totality *)
  unfold cmp_leb; destruct (cmp x y) eqn:H.
  1,2: now left. right; apply (cmp_swap ord) in H; rewrite H; easy.
Qed.

End Linear_order_function.
