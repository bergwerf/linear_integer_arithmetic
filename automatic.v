(* Automata automatic structures. *)

Require Vector.
Require Import Utf8 PeanoNat BinNat List Lia.
From larith Require Import tactics notations utilities vector.
From larith Require Import formulae automata regular.
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

(* Algorithm for deciding first-order realizability using finite automata. *)
Section Decide_wff_using_automata.

Variable atom domain : Type.
Variable Model : model atom domain.

Variable decode : list bool -> domain.
Variable encode : domain -> list bool.
Hypothesis decode_padding : ∀l n, decode l = decode (l ++ repeat false n).
Hypothesis decode_encode_id : ∀x, decode (encode x) = x.

Variable default : domain.
Hypothesis default_spec : ∀a Γ, Model Γ a <-> Model (Γ ++ [default]) a.

Definition vctx {n} (w : list (vec n)) : list domain :=
  Vector.to_list (Vector.map decode (transpose w)).

Definition Regular_wff φ := Σ n, Use Model φ n ×
  regular (λ w : list (vec n), Model |= (φ)[vctx w]).

Section Lemmas.

Lemma vctx_nil (w : list (vec 0)) :
  vctx w = [].
Proof.
unfold vctx; rewrite transpose_nil; easy.
Qed.

Lemma vctx_nth {n} (w : list (vec n)) i d :
  nth (findex i) (vctx w) d = decode (Vector.nth (transpose w) i).
Proof.
unfold vctx. rewrite <-Vector_nth_to_list.
apply Vector_nth_map.
Qed.

Lemma vctx_map_take {n} k (Hk : k <= n) w :
  vctx (map (Vector.take k Hk) w) = firstn k (vctx w).
Proof.
unfold vctx. rewrite <-transpose_take, Vector_map_take.
apply Vector_take_to_list.
Qed.

Lemma Realizes_ctx_default φ Γ :
  Model |= (φ)[Γ] <-> Model |= (φ)[Γ ++ [default]].
Proof.
revert Γ; induction φ; simpl; intros.
- apply default_spec.
- split; apply contra, IHφ.
- split. all: split; [apply (IHφ1 Γ)|apply (IHφ2 Γ)]; apply H.
- split; intros [x Hx]; exists x; apply (IHφ (x :: Γ)), Hx.
Qed.

Corollary Realizes_ctx_repeat_default φ Γ n :
  Model |= (φ)[Γ] <-> Model |= (φ)[Γ ++ repeat default n].
Proof.
induction n; simpl. now rewrite app_nil_r.
rewrite repeat_cons, IHn, app_assoc. apply Realizes_ctx_default.
Qed.

End Lemmas.

Theorem regular_ex φ n :
  regular (λ w : list (vec (S n)), Model |= (φ)[vctx w]) ->
  regular (λ w : list (vec n), Model |= (∃[φ])[vctx w]).
Proof.
intros [A det size fin dec spec].
pose(f (v : vec n) := [true ;; v; false ;; v]).
eapply Regular.
- apply Automata.pow_det.
- apply Automata.pow_size, Automata.proj_size with (f:=f), fin. apply dec.
- simpl; apply list_eq_dec, dec.
- intros; simpl.
  rewrite Automata.pow_spec, Automata.proj_spec; split.
  + (* Given a word for φ, determine a witness. *)
    intros [v [H1 H2]]. apply spec in H2.
    exists (decode (map Vector.hd v)).
    replace (_ :: vctx w) with (vctx v). easy. clear H2.
    unfold vctx; rewrite transpose_cons; simpl.
    rewrite Vector_to_list_cons; apply wd, wd, wd, wd.
    apply Forall2_map with (f:=f) in H1. induction H1; simpl. easy.
    rewrite IHForall2. destruct H as [R|[R|]]; subst; easy.
  + (* Given a witness, find a word for φ. *)
    intros [x Hx].
    (* Check encode x ;; transpose w. *)
Admitted.

Theorem construct_Regular_wff φ :
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
    Unshelve. apply le_max_l. apply le_max_r.
- (* Quantification: tail projection. *)
  destruct IHφ as [n [use reg]]; destruct n.
  + (* Edge case: the quantified formula is realized by an empty context. *)
    exists 0; split.
    eapply Use_ex, Use_weaken. apply use. lia.
    eapply regular_ext. apply reg.
    intros; simpl; rewrite vctx_nil; split.
    intros; exists default; apply Realizes_ctx_default in H; easy.
    intros [x Hx]; apply use in Hx; easy.
  + (* Remove top bit from the alphabet (non-deterministic projection). *)
    exists n; split.
    apply Use_ex, use.
    apply regular_ex, reg.
Qed.

Theorem Realizes_dec φ :
  Regular_wff φ -> {∃Γ, Model |= (φ)[Γ]} + {∀Γ, ¬ Model |= (φ)[Γ]}.
Proof.
intros [n [use reg]].
apply regular_dec with (alphabet:=enumerate_vectors n) in reg.
2: apply enumerate_vectors_spec. destruct reg as [Yes|No].
- (* There exists a context word that realizes φ. *)
  left; destruct Yes as [w Hw]. now exists (vctx w).
- (* There is no context word that realizes φ. *)
  right; intros Γ HΓ.
  (* Add default values to the context and restrict it to n values. *)
  apply Realizes_ctx_repeat_default with (n:=n), use in HΓ.
  assert(length (firstn n (Γ ++ repeat default n)) = n). {
    apply firstn_length_le. rewrite app_length, repeat_length. lia. }
  apply list_to_Vector in H as [Δ HΔ].
  (* Encode context as booleans, and generate a word. *)
  pose(bits := Vector.map encode Δ);
  pose(size := Vector.fold_right max (Vector.map (@length _) bits) 0);
  pose(letter i := Vector.map (λ l, nth i l false) bits);
  pose(word := map letter (seq 0 size)).
  (* This word gives a contradiction. *)
  apply No with (w:=word).
  replace (vctx word) with (Vector.to_list Δ).
  rewrite HΔ; apply HΓ. clear use No HΓ HΔ.
  (* Show that the word construction is valid. *)
  replace Δ with (Vector.map decode (transpose word)). easy.
  (* We need a better way to get letters. *)
Admitted.

End Decide_wff_using_automata.

Arguments Regular_wff {_ _}.
