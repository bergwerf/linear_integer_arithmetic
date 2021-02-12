(* Ordering using a comparison function. *)

From larith Require Import A_setup B1_utils.

Record Order {X} (cmp : X -> X -> comparison) := Order_spec {
  ord_eq : ∀x y, cmp x y = Eq <-> x = y;
  ord_opp : ∀x y, cmp x y = CompOpp (cmp y x);
  ord_lt_trans : ∀x y z, cmp x y = Lt -> cmp y z = Lt -> cmp x z = Lt;
}.

Arguments ord_eq {_ _}.
Arguments ord_opp {_ _}.
Arguments ord_lt_trans {_ _}.

Theorem ord_swap {X cmp} (ord : Order cmp) c (x y : X) :
  cmp x y = c <-> cmp y x = CompOpp c.
Proof.
rewrite (ord_opp ord).
apply CompOpp_iff.
Qed.

Theorem ord_trans {X cmp} (ord : Order cmp) c (x y z : X) :
  cmp x y = c -> cmp y z = c -> cmp x z = c.
Proof.
destruct c; intros.
- apply (ord_eq ord) in H, H0; subst; apply (ord_eq ord); reflexivity.
- apply (ord_lt_trans ord) with (y:=y); easy.
- apply (ord_swap ord); apply (ord_swap ord) in H, H0; simpl in *.
  apply (ord_lt_trans ord) with (y:=y); easy.
Qed.

Theorem ord_dec {X} (cmp : X -> X -> comparison) :
  Order cmp -> ∀x y : X, {x = y} + {x ≠ y}.
Proof.
intros [ord_eq _ _] x y.
destruct (cmp x y) eqn:H. left; apply ord_eq, H.
all: right; intros F; apply ord_eq in F; congruence.
Qed.

Section Ordering_small_domains.

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

End Ordering_small_domains.

Section Add_an_undefined_element.

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

End Add_an_undefined_element.

Section Lexicographic_ordering_of_pairs.

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
    apply (ord_eq ordA) in Ha; apply (ord_eq ordB) in Hb; subst; reflexivity.
  + intros H; injection H; intros.
    apply (ord_eq ordA) in H1; apply (ord_eq ordB) in H0.
    rewrite H0, H1; reflexivity.
- intros [a1 b1] [a2 b2]; simpl.
  destruct (cmpA a1 a2) eqn:Ha, (cmpB b1 b2) eqn:Hb;
  rewrite (ord_swap ordA) in Ha; rewrite (ord_swap ordB) in Hb;
  rewrite Ha, Hb; reflexivity.
- intros [a1 b1] [a2 b2] [a3 b3]; simpl; intros.
  apply cmp_pair_Lt in H, H0; apply cmp_pair_Lt;
  destruct H as [|[]], H0 as [|[]].
  + left; apply (ord_trans ordA) with (y:=a2); easy.
  + left; rewrite (ord_eq ordA) in H0; subst; easy.
  + left; rewrite (ord_eq ordA) in H; subst; easy.
  + right; split.
    now apply (ord_trans ordA) with (y:=a2).
    now apply (ord_trans ordB) with (y:=b2).
Qed.

End Lexicographic_ordering_of_pairs.

Section Lexicographic_ordering_of_lists.

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

End Lexicographic_ordering_of_lists.
