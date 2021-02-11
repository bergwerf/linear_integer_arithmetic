(* Construction of orderings. *)

Require Import Utf8 List.
From larith Require Import tactics notations utilities.

Record Order {X} (cmp : X -> X -> comparison) := Order_spec {
  ord_eq : ∀x y, cmp x y = Eq <-> x = y;
  ord_opp : ∀x y, cmp x y = CompOpp (cmp y x);
  ord_trans : ∀c x y z, cmp x y = c -> cmp y z = c -> cmp x z = c;
}.

Arguments ord_eq {_ _}.
Arguments ord_opp {_ _}.
Arguments ord_trans {_ _}.

Section Lexicographic_order_on_pairs.

Variable A B : Type.
Variable cmpA : A -> A -> comparison.
Variable cmpB : B -> B -> comparison.
Variable ordA : Order cmpA.
Variable ordB : Order cmpB.

Definition lex ab1 ab2 :=
  match cmpA (fst ab1) (fst ab2) with
  | Eq => cmpB (snd ab1) (snd ab2)
  | Lt => Lt
  | Gt => Gt
  end.

Theorem lecicopraphic_order :
  Order lex.
Proof.
unfold lex; split.
- intros [xa xb] [ya yb]; simpl; split.
  + destruct (cmpA xa ya) eqn:Ha, (cmpB xb yb) eqn:Hb; try easy.
    apply (ord_eq ordA) in Ha; apply (ord_eq ordB) in Hb; subst; reflexivity.
  + intros H; injection H; intros.
    apply (ord_eq ordA) in H1; apply (ord_eq ordB) in H0.
    rewrite H0, H1; reflexivity.
- intros [xa xb] [ya yb]; simpl.
  destruct (cmpA xa ya) eqn:Ha, (cmpB xb yb) eqn:Hb;
  rewrite (ord_opp ordA) in Ha; rewrite (ord_opp ordB) in Hb;
  apply CompOpp_iff in Ha, Hb; rewrite Ha, Hb; reflexivity.
- intros c [xa xb] [ya yb] [za zb]; simpl.
  (* Brute-force case analysis is a bit too heavy. *)
Admitted.

End Lexicographic_order_on_pairs.
