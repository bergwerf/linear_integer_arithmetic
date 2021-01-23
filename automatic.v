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

Theorem transpose_take {n} k (Hk : k <= n) mat :
  Vector.take k Hk (transpose mat) = transpose (map (Vector.take k Hk) mat).
Proof.
induction mat; simpl. apply Vector_take_const.
rewrite <-IHmat; apply Vector_take_map2_cons.
Qed.

End Matrix_transposition.

Arguments transpose {_ _}.

(* Algorithm for deciding first-order realizability using finite automata. *)
Section Decide_wff_using_automata.

Variable atom domain : Type.
Variable Model : model atom domain.

Variable decode : list bool -> domain.
Variable encode : domain -> list bool.

Definition vctx {n} (w : list (vec n)) : list domain :=
  Vector.to_list (Vector.map decode (transpose w)).

Definition Regular_wff φ := Σ n, Use Model φ n ×
  regular (λ w : list (vec n), Model |= (φ)[vctx w]).

Theorem vctx_nth {n} (w : list (vec n)) i d :
  nth (findex i) (vctx w) d = decode (Vector.nth (transpose w) i).
Proof.
unfold vctx. rewrite <-Vector_nth_to_list. apply Vector_nth_map.
Qed.

Theorem vctx_map_take {n} k (Hk : k <= n) w :
  vctx (map (Vector.take k Hk) w) = firstn k (vctx w).
Proof.
unfold vctx. rewrite <-transpose_take, Vector_map_take.
apply Vector_take_to_list.
Qed.

Theorem regular_wff_dec φ :
  Regular_wff φ -> {∃Γ, Model |= (φ)[Γ]} + {∀Γ, ¬ Model |= (φ)[Γ]}.
Proof.
intros [n [use reg]].
apply regular_dec with (alphabet:=enumerate_vectors n) in reg.
2: apply enumerate_vectors_spec. destruct reg.
- left. destruct e as [w Hw]. now exists (vctx w).
- right. intros Γ HΓ. apply use in HΓ; eapply n0.
  admit.
Admitted.

Theorem regular_wff φ :
  (∀a, Regular_wff (wff_atom a)) -> Regular_wff φ.
Proof.
intros regular_atoms.
induction φ; simpl.
- (* Atomic formulae: regular by assumption. *)
  apply regular_atoms.
- (* Negation: flip accept states. *)
  destruct IHφ as [n [use reg]]; exists n; split.
  apply Use_not, use. apply regular_negation, reg.
- (* Conjunction: project on a common alphabet and use the product. *)
  destruct IHφ1 as [n1 [use1 reg1]], IHφ2 as [n2 [use2 reg2]].
  exists (max n1 n2); split; simpl.
  + apply Use_and; eapply Use_weaken.
    apply use1. apply le_max_l. apply use2. apply le_max_r.
  + apply regular_conjunction; eapply regular_proj;
    [apply reg1|intros|apply reg2|intros]; simpl.
    all: rewrite vctx_map_take; easy.
- (* Quantification: tail projection. *)
  admit.
Abort.

End Decide_wff_using_automata.

Arguments Regular_wff {_ _}.
