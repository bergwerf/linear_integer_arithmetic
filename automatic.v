(* Building automata for automatic structures. *)

Require Vector.
Require Import Utf8 PeanoNat BinNat List Lia.
From larith Require Import tactics notations utilities order vector.
From larith Require Import formulae automata regular.

(* Algorithm for deciding first-order realizability using finite automata. *)
Section Decide_wff_using_automata.

Variable atom domain : Type.
Variable Model : model atom domain.
Variable default : domain.
Hypothesis default_spec : ∀a Γ, Model a Γ <-> Model a (Γ ++ [default]).

Variable decode : list bool -> domain.
Variable encode : domain -> list bool.
Hypothesis decode_encode_id : ∀x, decode (encode x) = x.
Hypothesis decode_padding : ∀l, decode (l ++ [false]) = decode l.

Definition vctx {n} (w : list (vec n)) : list domain :=
  vlist (vmap decode (vmap vlist (transpose (voflist w)))).

Definition Automatic φ := Σ n, Use Model φ n ×
  regular (λ w : list (vec n), Model |= (φ)[vctx w]).

Section Useful_lemmas.

Theorem Realizes_ctx_default φ Γ :
  Model |= (φ)[Γ] <-> Model |= (φ)[Γ ++ [default]].
Proof.
revert Γ; induction φ; simpl; intros.
- apply default_spec.
- split; apply contra, IHφ.
- split. all: split; [apply (IHφ1 Γ)|apply (IHφ2 Γ)]; apply H.
- split; intros [x Hx]; exists x; apply (IHφ (x :: Γ)), Hx.
Qed.

Theorem Realizes_ctx_repeat_default φ Γ n :
  Model |= (φ)[Γ] <-> Model |= (φ)[Γ ++ repeat default n].
Proof.
induction n; simpl. now rewrite app_nil_r.
rewrite repeat_cons, IHn, app_assoc. apply Realizes_ctx_default.
Qed.

Theorem decode_repeat_padding l k :
  decode (l ++ repeat false k) = decode l.
Proof.
induction k; simpl. now rewrite app_nil_r.
rewrite repeat_cons, app_assoc, decode_padding, IHk; reflexivity.
Qed.

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
pose(maxlen := lmax (map (@length _) (map encode Γ))).
pose(matrix := vmap (cast false maxlen) binary).
exists (vlist (transpose matrix)); unfold vctx.
apply voflist_vlist_id; rewrite transpose_transpose_id.
unfold matrix, binary; rewrite <-?map_vlist, vlist_voflist_id.
erewrite ?map_map, map_ext_in. apply map_id.
(* Show that casting did not change the value. *)
intros x Hx; simpl. rewrite vlist_cast.
rewrite decode_repeat_padding; apply decode_encode_id.
apply lmax_in, in_map, in_map, Hx.
Qed.

End Useful_lemmas.

(* Existential quantification is the most involved construction. *)
Section Regularity_of_existential_quantification.

Notation glue hs ts := (map2 (λ h t, h ;; t) hs ts).

Lemma map_vhd_glue {X n} hs (ts : list (Vector.t X n)) :
  length hs <= length ts -> map vhd (glue hs ts) = hs.
Proof.
revert ts; induction hs; destruct ts; simpl; intros; try easy.
rewrite IHhs. easy. apply le_S_n, H.
Qed.

Lemma map_vtl_glue {X n} hs (ts : list (Vector.t X n)) :
  length ts <= length hs -> map vtl (glue hs ts) = ts.
Proof.
revert ts; induction hs; destruct ts; simpl; intros; try easy.
rewrite IHhs. easy. apply le_S_n, H.
Qed.

Variable n : nat.
Notation zero := (vrepeat false n).
Definition proj (v : vec n) := [true ;; v; false ;; v].

Lemma Image_proj_map_vtl v w :
  Automata.Image proj w v <-> map vtl v = w.
Proof.
unfold Automata.Image; rewrite Forall2_map; split.
- intros H; induction H; simpl. easy. inv H; inv H1.
- revert w; induction v; destruct w; simpl; try easy.
  intros H; inv H; apply Forall2_cons.
  + apply Vector.caseS' with (v0:=a); intros [] a'; auto.
  + apply IHv; easy.
Qed.

Lemma decode_transpose_padding w k :
  vmap decode (vmap vlist (transpose (voflist (w ++ repeat zero k)))) =
  vmap decode (vmap vlist (transpose (voflist w))).
Proof.
rewrite transpose_convert with (mat':=voflist w +++ vrepeat zero k).
2: rewrite vlist_app, ?vlist_voflist_id, vlist_vrepeat; reflexivity.
rewrite transpose_app, transpose_vrepeat_vrepeat, vmap2_append_vrepeat.
rewrite ?Vector.map_map; apply Vector.map_ext_in; intros v Hv.
rewrite vlist_app, vlist_vrepeat; apply decode_repeat_padding.
Qed.

Theorem regular_ex φ :
  regular (λ w : list (vec (S n)), Model |= (φ)[vctx w]) ->
  regular (λ w : list (vec n), Model |= (∃[φ])[vctx w]).
Proof.
intros [A size fin spec det cmp ord].
assert(dec := ord_dec cmp ord); eapply Regular with
(r_fsa:=Automata.sat _ (Automata.proj _ A _ proj) zero size dec).
- apply fin.
- intros; simpl.
  (* Rewrite specification. *)
  etransitivity. apply Automata.sat_spec, fin.
  etransitivity. apply ex_iff. intros; apply Automata.proj_spec. simpl.
  (* Prove correctness. *)
  split.
  + (* Given a word for φ, compute the witness. *)
    intros [k [v [Himage Hv]]]. apply spec in Hv.
    exists (decode (map Vector.hd v)).
    erewrite wd. apply Hv. clear Hv.
    (* Rewrite until decode_transpose_padding is left. *)
    unfold vctx; rewrite transpose_cons; simpl.
    rewrite vlist_cons, <-map_vlist with (f:=vhd), vlist_voflist_id.
    apply wd, wd; erewrite transpose_convert with (mat:=vmap _ _).
    2: rewrite vmap_voflist, vlist_voflist_id.
    2: apply Image_proj_map_vtl, Himage.
    symmetry; apply decode_transpose_padding.
  + (* Given a witness, construct a word for φ. *)
    intros [x Hx].
    pose(y  := encode x);
    pose(hs := y ++ repeat false (length w - length y));
    pose(ts := w ++ repeat zero (length y - length w));
    exists (length y - length w), (glue hs ts); split.
    * (* Show that the word is in the image. *)
      apply Image_proj_map_vtl, map_vtl_glue.
      unfold hs, y; rewrite ?app_length, ?repeat_length; lia.
    * (* Show that the word is accepted. *)
      apply spec; erewrite wd. apply Hx. clear Hx.
      (* Rewrite until decode_transpose_padding is left. *)
      unfold vctx; rewrite transpose_cons; simpl.
      rewrite vlist_cons, <-map_vlist with (f:=vhd), vlist_voflist_id.
      rewrite map_vhd_glue at 1; unfold hs, y at 1.
      rewrite decode_repeat_padding, decode_encode_id; apply wd.
      erewrite transpose_convert.
      2: rewrite vmap_voflist, map_vtl_glue.
      2: rewrite vlist_voflist_id; reflexivity.
      apply wd, decode_transpose_padding.
      all: unfold ts, hs, y; rewrite ?app_length, ?repeat_length; lia.
- apply None.
- apply ord.
Defined.

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
  apply Use_not, use. admit.
- (* Conjunction: project on a common alphabet and use the product. *)
  destruct IHφ1 as [n1 [use1 reg1]], IHφ2 as [n2 [use2 reg2]].
  exists (max n1 n2); split; simpl.
  + apply Use_and; eapply Use_weaken.
    apply use1. apply Nat.le_max_l. apply use2. apply Nat.le_max_r.
  + apply regular_conjunction; eapply regular_proj;
    [apply reg1|intros|apply reg2|intros]; simpl.
    all: rewrite vctx_map_take; easy.
    Unshelve. apply Nat.le_max_l. apply Nat.le_max_r.
- (* Quantification: tail projection. *)
  destruct IHφ as [n [use reg]]; destruct n.
  + (* Edge case: the quantified formula is realized by an empty context. *)
    exists 0; split.
    eapply Use_ex, Use_weaken. apply use. auto.
    eapply regular_ext. apply reg.
    intros; simpl; rewrite vctx_nil; split.
    intros; exists default; apply Realizes_ctx_default in H; easy.
    intros [x Hx]; apply use in Hx; easy.
  + (* Remove top bit from the alphabet (non-deterministic projection). *)
    exists n; split.
    apply Use_ex, use.
    apply regular_ex, reg.
Admitted.

Theorem Automatic_Realizes_dec φ :
  Automatic φ -> (Σ Γ, Model |= (φ)[Γ]) + {∀Γ, Model |= (¬`φ)[Γ]}.
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
Defined.

Corollary automatic_structure_dec φ :
  (∀a, Automatic (wff_atom a)) ->
  (Σ Γ, Model |= (φ)[Γ]) + {∀Γ, Model |= (¬`φ)[Γ]}.
Proof.
intros H; apply Automatic_Realizes_dec, automatic_structure, H.
Defined.

End Decide_wff_using_automata.

Arguments Automatic {_ _}.
