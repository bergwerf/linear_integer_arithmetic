(* Lemmas on various topics. *)

Require Import Utf8 List Lia.
From larith Require Import tactics notations.
Import ListNotations.

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

End Propositions.

End Laws_of_logic.

Section Lemmas_about_lists.

Lemma list_prod_nil_r {X Y} (l : list X) :
  @list_prod X Y l nil = nil.
Proof.
now induction l.
Qed.

Lemma list_singleton {X} (l : list X) :
  length l = 1 -> ∃x, l = [x].
Proof.
intros. destruct l. easy. destruct l.
now exists x. easy.
Qed.

Lemma in_singleton {X} (x x' : X) :
  In x [x'] -> x = x'.
Proof.
intros H; now inv H.
Qed.

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

End Lemmas_about_lists.

Arguments remove_None {_}.
