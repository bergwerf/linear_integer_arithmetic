(* Lemmas on various topics. *)

Require Import Utf8 List.
From larith Require Import tactics notations.

Section Lemmas_about_lists.

Section List_products.

Lemma list_prod_nil_r {T S} (l : list T) :
  @list_prod T S l nil = nil.
Proof.
now induction l.
Qed.

End List_products.

End Lemmas_about_lists.
