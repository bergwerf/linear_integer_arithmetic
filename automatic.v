(* Automata automatic structures. *)

Require Vector.
Require Import Utf8 PeanoNat BinNat List.
From larith Require Import tactics notations utilities.
From larith Require Import formulae regular.
Import Nat ListNotations.

(* Finite-length vectors form a finite alphabet. *)
Section Finite_vector_alphabet.

Fixpoint enumerate_vectors n : list (vec n) :=
  match n with
  | 0 => [⟨⟩]
  | S m =>
    let vs := enumerate_vectors m in
    map (vcons false m) vs ++
    map (vcons true m) vs
  end.

Theorem enumerate_vectors_spec n (v : vec n) :
  In v (enumerate_vectors n).
Proof.
induction v; simpl. now left.
apply in_app_iff; destruct h; [right|left]; apply in_map, IHv.
Qed.

End Finite_vector_alphabet.

(* Transpose a vector list. *)
Section Matrix_transposition.

Variable T : Type.

(* Convert from a list of collumn vectors to a vector of row lists. *)
Fixpoint transpose {n} (mat : list (Vector.t T n)) : Vector.t (list T) n :=
  match mat with
  | []     => Vector.const [] n
  | v :: m => Vector.map2 cons v (transpose m)
  end.

Theorem transpose_cons {n} (mat : list (Vector.t T (S n))) :
  transpose mat = map Vector.hd mat ;; transpose (map Vector.tl mat).
Proof.
induction mat; simpl. easy.
apply Vector.caseS' with (v:=a).
intros; now rewrite IHmat.
Qed.

Theorem transpose_nth {n} (mat : list (Vector.t T n)) (i : Fin.t n)  :
  Vector.nth (transpose mat) i = map (λ v, Vector.nth v i) mat.
Proof.
induction mat; simpl. now induction i.
rewrite <-IHmat. apply Vector_nth_map2_cons.
Qed.

End Matrix_transposition.

Arguments transpose {_ _}.

(* Algorithm for deciding first-order realizability using finite automata. *)
Section Decide_wff_using_automata.

Variable atom domain : Type. 
Variable value : list bool -> domain.
Variable Model : model atom domain.

Definition vctx {n} (w : list (vec n)) : list domain :=
  Vector.to_list (Vector.map value (transpose w)).

Lemma vctx_nth {n} (w : list (vec n)) i d :
  nth (findex i) (vctx w) d = value (Vector.nth (transpose w) i).
Proof.
unfold vctx. rewrite <-Vector_nth_to_list. apply Vector_nth_map.
Qed.

Definition Regular_wff φ := Σ n, Use Model φ n ×
  regular (λ w : list (vec n), Model |= (φ)[vctx w]).

Hypothesis hypothesis : ∀a, Regular_wff (wff_atom _ a).

Theorem regular_wff φ :
  Regular_wff φ.
Proof.
induction φ; simpl.
- (* Atomic formulae: we assume these are regular. *)
  apply hypothesis.
- (* Negation: flip accept states. *)
  destruct IHφ as [n [use reg]]; exists n; split.
  + split; simpl; apply contra, use.
  + simpl; apply regular_neg, reg.
- (* Conjunction: project on a common alphabet and use the product. *)
  destruct IHφ1 as [n1 [use1 reg1]], IHφ2 as [n2 [use2 reg2]].
  exists (max n1 n2); split; simpl. 2: eapply regular_conj.
  + admit.
  + eapply regular_proj with (f:=Vector.take n1 (le_max_l n1 n2)).
    apply reg1. intros; simpl. admit.
  + eapply regular_proj with (f:=Vector.take n2 (le_max_r n1 n2)).
    apply reg2. intros; simpl. admit.
- (* Quantification: tail projection. *)
  admit.
Abort.

End Decide_wff_using_automata.
