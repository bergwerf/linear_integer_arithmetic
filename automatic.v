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
    map (Vector.cons _ false m) vs ++
    map (Vector.cons _ true m) vs
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
Hypothesis decode_encode_id : ∀x, decode (encode x) = x.
Hypothesis decode_padding : ∀l n, decode (l ++ repeat false n) = decode l.

Variable default : domain.
Hypothesis default_spec : ∀a Γ, Model a Γ <-> Model a (Γ ++ [default]).

Definition vctx {n} (w : list (vec n)) : list domain :=
  vlist (vmap decode (vmap vlist (transpose (voflist w)))).

Definition Automatic φ := Σ n, Use Model φ n ×
  regular (λ w : list (vec n), Model |= (φ)[vctx w]).

Section Preliminary_results.

Theorem vctx_nil (w : list (vec 0)) :
  vctx w = [].
Proof.
unfold vctx; rewrite transpose_nil; easy.
Qed.

Theorem vctx_nth n (w : list (vec n)) i d :
  nth (findex i) (vctx w) d = decode (map (λ v, vnth v i) w).
Proof.
unfold vctx; rewrite <-vnth_nth_findex, ?vnth_vmap.
rewrite vnth_transpose, <-map_vlist, vlist_voflist_id; reflexivity.
Qed.

Theorem vctx_map_take n k (Hk : k <= n) w :
  vctx (map (vtake k Hk) w) = firstn k (vctx w).
Proof.
unfold vctx.
rewrite <-vtake_firstn with (Hk:=Hk); apply wd.
rewrite <-vmap_vtake; apply wd.
rewrite <-vmap_vtake, vtake_transpose.
apply transpose_convert; rewrite vlist_voflist_id.
rewrite <-map_vlist, vlist_voflist_id; reflexivity.
Qed.

Theorem vctx_surj Γ :
  ∃w : list (vec (length Γ)), vctx w = Γ.
Proof.
pose(binary := vmap encode (voflist Γ)).
pose(maxlen := lmax (map (@length _) (vlist binary))).
pose(matrix := vmap (cast false maxlen) binary).
exists (vlist (transpose matrix)).
Admitted.

Theorem Realizes_ctx_default φ Γ :
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

End Preliminary_results.

(* Existential quantification is the most involved construction. *)
Section Regularity_of_existential_quantification.

Lemma map_vhd_map2_cons {X n} hs (ts : list (Vector.t X n)) :
  map vhd (map2 (λ h t, h ;; t) hs ts) = hs.
Proof.
Admitted.

Lemma map_vtl_map2_cons {X n} hs (ts : list (Vector.t X n)) :
  map vtl (map2 (λ h t, h ;; t) hs ts) = ts.
Proof.
Admitted.

Theorem regular_ex φ n :
  regular (λ w : list (vec (S n)), Model |= (φ)[vctx w]) ->
  regular (λ w : list (vec n), Model |= (∃[φ])[vctx w]).
Proof.
intros [A det size [Q [Q_len Q_spec]] dec spec].
pose(zero := vrepeat false n);
pose(pr (v : vec n) := [true ;; v; false ;; v]).
eapply Regular.
- apply Automata.pow_det
  with (A:=Automata.sat _ (Automata.proj _ A _ pr) zero size).
- apply Automata.pow_size.
- simpl; apply Automata.pow_dec.
- intros; simpl.
  (* Transform into automaton specification. *)
  rewrite Automata.pow_spec, Automata.sat_spec.
  rewrite ex_iff. 2: intros; apply Automata.proj_spec. simpl.
  (* Prove specification hypotheses. *)
  4: apply Q_spec. 3: exists Q; easy. 2: apply dec.
  (* Prove correctness. *)
  split.
  + (* Given a word for φ, compute the witness. *)
    intros [k [v [Himage Hv]]]. apply spec in Hv.
    exists (decode (map Vector.hd v)).
    unfold Automata.Image in Himage.
    erewrite wd. apply Hv. clear Hv.
    (* Expose transposition and remove head. *)
    unfold vctx; rewrite transpose_cons; simpl.
    rewrite vlist_cons, <-map_vlist with (f:=vhd), vlist_voflist_id.
    apply wd, wd.
    (* Replace (vmap vtl (voflist v)) with (voflist w ++ vrepeat zero k) *)
    (* Show that decode erases all added zero vectors. *)
    admit.
  + (* Given a witness, construct a word for φ. *)
    intros [x Hx].
    pose(xw  := encode x).
    pose(k   := length xw - length w).
    pose(xw' := xw ++ repeat false (length w)).
    pose(w'  := w ++ repeat zero k).
    exists k, (map2 (λ h t, h ;; t) xw' w'); split.
    * (* Show that the word is in the image. *)
      (* This goal should be a separate theorem. *)
      admit.
    * (* Show that the word is accepted. *)
      apply spec; erewrite wd. apply Hx. clear Hx.
      (* Expose transposition and reduce. *)
      unfold vctx; rewrite transpose_cons; simpl.
      rewrite vlist_cons, <-map_vlist with (f:=vhd), vlist_voflist_id.
      rewrite map_vhd_map2_cons; unfold xw', xw at 1.
      rewrite decode_padding, decode_encode_id; apply wd.
      erewrite transpose_convert.
      2: rewrite vmap_voflist, map_vtl_map2_cons.
      2: rewrite vlist_voflist_id; reflexivity.
      apply wd; unfold w'.
      (* This goal is similar to an earlier one. *)
Admitted.

End Regularity_of_existential_quantification.

Theorem automatic_structure φ :
  (∀a, Automatic (wff_atom a)) -> Automatic φ.
Proof.
intros automatic_atoms.
induction φ; simpl.
- (* Atomic formulae: regular by assumption. *)
  apply automatic_atoms.
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

Theorem Automatic_Realizes_dec φ :
  Automatic φ -> {∃Γ, Model |= (φ)[Γ]} + {∀Γ, ¬ Model |= (φ)[Γ]}.
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
  remember (firstn n (Γ ++ repeat default n)) as Δ.
  (* Now determine a context word and apply a contradiction. *)
  destruct vctx_surj with (Γ:=Δ) as [w Hw].
  replace n with (length Δ) in No.
  + rewrite <-Hw in HΓ; apply No in HΓ; easy.
  + subst; apply firstn_length_le. rewrite app_length, repeat_length. lia.
Qed.

End Decide_wff_using_automata.

Arguments Automatic {_ _}.
