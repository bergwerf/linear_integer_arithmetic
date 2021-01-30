(* Vector and matrix utilities. *)

Require Vector.
Require Import Utf8 PeanoNat List Lia.
From larith Require Import tactics notations.
Import ListNotations.

Module Vector_notations.

Notation vhd := (Vector.hd).
Notation vtl := (Vector.tl).
Notation vnth := (Vector.nth).
Notation vmap := (Vector.map).
Notation vmap2 := (Vector.map2).
Notation vtake := (Vector.take).
Notation vlist := (Vector.to_list).
Notation voflist := (Vector.of_list).
Notation vrepeat := (Vector.const).
Notation vlist_voflist_id := (Vector.to_list_of_list_opp).

Notation "⟨ ⟩" := (Vector.nil _) (format "⟨ ⟩").
Notation "h ;; t" := (Vector.cons _ h _ t)
  (at level 60, right associativity, format "h  ;;  t").

Notation "⟨ x ⟩" := (x ;; ⟨⟩).
Notation "⟨ x ; y ; .. ; z ⟩" :=
  (Vector.cons x _ (Vector.cons y _ .. (Vector.cons z _ (nil _)) ..)).

End Vector_notations.
Export Vector_notations.

Section Type_agnostic.

Variable X : Type.
Notation vec := (Vector.t X).

Section Lemmas.

Lemma vlist_cons n hd (tl : vec n) :
  vlist (hd ;; tl) = hd :: vlist tl.
Proof.
easy.
Qed.

End Lemmas.

Section Nth.

Fixpoint fin n i : Fin.t (S n) :=
  match n with
  | 0   => Fin.F1
  | S m =>
    match i with
    | 0   => Fin.F1
    | S j => Fin.FS (fin m j)
    end
  end.

Fixpoint findex {n} (i : Fin.t n) :=
  match i with
  | Fin.F1 => 0
  | Fin.FS j => S (findex j)
  end.

Theorem fin_spec n i :
  i <= n -> findex (fin n i) = i.
Proof.
revert i; induction n, i; simpl; intros; try easy.
rewrite IHn. easy. lia.
Qed.

Theorem vnth_nth_findex n (v : vec n) (i : Fin.t n) d :
  vnth v i = nth (findex i) (vlist v) d.
Proof.
induction v. easy.
now apply Fin.caseS' with (p:=i).
Qed.

End Nth.

Section Mapping.

Variable Y : Type.
Variable f : X -> Y.

Theorem vnth_vmap n (v : vec n) (i : Fin.t n) :
  vnth (vmap f v) i = f (vnth v i).
Proof.
induction v. easy.
now apply Fin.caseS' with (p:=i).
Qed.

Theorem vmap_vtake n v k (Hk : k <= n) :
  vmap f (vtake k Hk v) = vtake k Hk (vmap f v).
Proof.
revert Hk; revert k; induction v as [|hd n tl];
intros; destruct k; simpl; try easy.
now rewrite IHtl.
Qed.

Theorem map_vlist n (v : vec n) :
  map f (vlist v) = vlist (vmap f v).
Proof.
induction v; simpl. easy.
unfold vlist in *; rewrite IHv; easy.
Qed.

End Mapping.

Section Take.

Theorem vtake_vrepeat n k (Hk : k <= n) (c : X) :
  vtake k Hk (vrepeat c n) = vrepeat c k.
Proof.
revert Hk; revert n; induction k; intros.
easy. destruct n; simpl. easy. now rewrite IHk.
Qed.

Theorem vtake_firstn n (v : vec n) k (Hk : k <= n) :
  vlist (vtake k Hk v) = firstn k (vlist v).
Proof.
revert Hk; revert k; induction v as [|hd n tl];
intros; destruct k; try easy.
simpl vtake; rewrite ?vlist_cons.
simpl; now rewrite IHtl.
Qed.

End Take.

Section Casting.

Variable default : X.

Fixpoint cast n (l : list X) : vec n :=
  match n with
  | 0   => ⟨⟩
  | S m =>
    match l with
    | []      => default ;; cast m []
    | x :: l' => x ;; cast m l'
    end
  end.

End Casting.

End Type_agnostic.

Section Matrix_transposition.

Variable X : Type.
Notation vec := (Vector.t X).
Notation matrix m n := (Vector.t (vec m) n).

(* Convert from a list of collumn vectors to a vector of row lists. *)
Fixpoint transpose {m n} (mat : matrix m n) : matrix n m :=
  match mat with
  | ⟨⟩     => vrepeat ⟨⟩ m
  | v ;; m => vmap2 (λ h t, h ;; t) v (transpose m)
  end.

Theorem transpose_nil n (mat : matrix 0 n) :
  transpose mat = ⟨⟩.
Proof.
induction mat; simpl. easy.
now rewrite IHmat; apply Vector.case0 with (v:=h).
Qed.

Theorem transpose_cons m n (mat : matrix (S m) n) :
  transpose mat = vmap vhd mat ;; transpose (vmap vtl mat).
Proof.
induction mat; simpl. easy.
apply Vector.caseS' with (v:=h).
intros; now rewrite IHmat.
Qed.

Lemma vmap_vhd_vmap2_cons m n (hs : vec n) (ts : matrix m n) :
  vmap vhd (vmap2 (λ h t, h ;; t) hs ts) = hs.
Proof.
induction hs.
apply Vector.case0 with (v:=ts); easy.
apply Vector.caseS' with (v:=ts); intros; simpl; rewrite IHhs; easy.
Qed.

Lemma vmap_vtl_vmap2_cons m n (hs : vec n) (ts : matrix m n) :
  vmap vtl (vmap2 (λ h t, h ;; t) hs ts) = ts.
Proof.
induction hs.
apply Vector.case0 with (v:=ts); easy.
apply Vector.caseS' with (v:=ts); intros; simpl; rewrite IHhs; easy.
Qed.

Theorem transpose_transpose m n (mat : matrix m n) :
  transpose (transpose mat) = mat.
Proof.
revert mat; revert m; induction n; intros.
- apply Vector.case0 with (v:=mat); clear mat; simpl.
  induction m; simpl. easy. now rewrite IHm.
- rewrite transpose_cons.
  apply Vector.caseS' with (v:=mat); intros; simpl.
  now rewrite vmap_vhd_vmap2_cons, vmap_vtl_vmap2_cons, IHn.
Qed.

Lemma vnth_vmap2_cons m n (hs : vec n) (ts : matrix m n) i :
  vnth (vmap2 (λ h t, h ;; t) hs ts) i =
  vnth hs i ;; vnth ts i.
Proof.
induction ts as [|t n ts]. easy.
apply Vector.caseS' with (v:=hs); clear hs; intros h hs.
simpl vmap2. eapply Fin.caseS' with (p:=i); simpl.
easy. apply IHts.
Qed.

Theorem vnth_transpose m n (mat : matrix m n) (i : Fin.t m)  :
  vnth (transpose mat) i = vmap (λ v, vnth v i) mat.
Proof.
induction mat; simpl. apply Vector.const_nth.
rewrite <-IHmat, vnth_vmap2_cons; reflexivity.
Qed.

Lemma vtake_vmap2_cons m n (hs : vec n) (ts : matrix m n) k (Hk : k <= n) :
  vtake k Hk (vmap2 (λ h t, h ;; t) hs ts) =
  vmap2 (λ h t, h ;; t) (vtake k Hk hs) (vtake k Hk ts).
Proof.
revert Hk; revert k; induction ts as [|t n ts];
intros; destruct k; try easy.
apply Vector.caseS' with (v:=hs); clear hs; intros h hs.
simpl; rewrite IHts; easy.
Qed.

Theorem vtake_transpose m n (mat : matrix m n) k (Hk : k <= m) :
  vtake k Hk (transpose mat) = transpose (vmap (vtake k Hk) mat).
Proof.
induction mat; simpl. apply vtake_vrepeat.
now rewrite <-IHmat, vtake_vmap2_cons.
Qed.

Lemma vmap_vlist_vmap2_cons m n (hs : vec n) (ts : matrix m n) :
  vmap vlist (vmap2 (λ h t, h ;; t) hs ts) = vmap2 cons hs (vmap vlist ts).
Proof.
induction hs.
apply Vector.case0 with (v:=ts); easy.
apply Vector.caseS' with (v:=ts); intros.
simpl; rewrite IHhs; easy.
Qed.

Theorem transpose_convert m n n' (mat : matrix m n) (mat' : matrix m n') :
  vlist mat = vlist mat' ->
  vmap vlist (transpose mat) = vmap vlist (transpose mat').
Proof.
revert mat'; revert n'; induction mat; destruct mat'; simpl; try easy.
intros H; inv H. apply IHmat in H2.
rewrite ?vmap_vlist_vmap2_cons; congruence.
Qed.

End Matrix_transposition.

Arguments cast {_}.
Arguments transpose {_ _ _}.
