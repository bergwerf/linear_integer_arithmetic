(* Vector and matrix utilities. *)

Require Vector.
Require Import Utf8 PeanoNat List Lia.
From larith Require Import tactics notations.
Import ListNotations.

Section Type_agnostic.

Variable X : Type.
Notation vec := (Vector.t X).

Section Lemmas.

Lemma Vector_to_list_cons {n} hd (tl : vec n) :
  Vector.to_list (hd ;; tl) = hd :: Vector.to_list tl.
Proof.
easy.
Qed.

Lemma list_to_Vector (l : list X) n :
  length l = n -> Σ v : vec n, Vector.to_list v = l.
Proof.
revert n; induction l; simpl; intros.
- subst; now exists ⟨⟩.
- destruct n. easy. injection H; intros.
  apply IHl in H0 as [v Hv]; exists (a ;; v).
  now rewrite Vector_to_list_cons, Hv.
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

Theorem Vector_nth_to_list {n} (v : vec n) (i : Fin.t n) d :
  Vector.nth v i = nth (findex i) (Vector.to_list v) d.
Proof.
induction v. easy.
now apply Fin.caseS' with (p:=i).
Qed.

End Nth.

Section Mapping.

Variable Y : Type.
Variable f : X -> Y.

Theorem Vector_nth_map {n} (v : vec n) (i : Fin.t n) :
  Vector.nth (Vector.map f v) i = f (Vector.nth v i).
Proof.
induction v. easy.
now apply Fin.caseS' with (p:=i).
Qed.

Theorem Vector_map_take {n} v k (Hk : k <= n) :
  Vector.map f (Vector.take k Hk v) = Vector.take k Hk (Vector.map f v).
Proof.
revert Hk; revert k; induction v as [|hd n tl];
intros; destruct k; simpl; try easy.
now rewrite IHtl.
Qed.

Theorem Vector_nth_map2_cons {n} (hs : vec n) ts i :
  Vector.nth (Vector.map2 cons hs ts) i =
  Vector.nth hs i :: Vector.nth ts i.
Proof.
induction ts as [|t n ts]. easy.
apply Vector.caseS' with (v:=hs); clear hs; intros h hs.
simpl Vector.map2. eapply Fin.caseS' with (p:=i); simpl.
easy. apply IHts.
Qed.

End Mapping.

Section Take.

Theorem Vector_take_const {n} k (Hk : k <= n) (c : X) :
  Vector.take k Hk (Vector.const c n) = Vector.const c k.
Proof.
revert Hk; revert n; induction k; intros.
easy. destruct n; simpl. easy. now rewrite IHk.
Qed.

Theorem Vector_take_map2_cons {n} (hs : vec n) ts k (Hk : k <= n) :
  Vector.take k Hk (Vector.map2 cons hs ts) =
  Vector.map2 cons (Vector.take k Hk hs) (Vector.take k Hk ts).
Proof.
revert Hk; revert k; induction ts as [|t n ts];
intros; destruct k; try easy.
apply Vector.caseS' with (v:=hs); clear hs; intros h hs.
simpl; rewrite IHts; easy.
Qed.

Theorem Vector_take_to_list {n} (v : vec n) k (Hk : k <= n) :
  Vector.to_list (Vector.take k Hk v) = firstn k (Vector.to_list v).
Proof.
revert Hk; revert k; induction v as [|hd n tl];
intros; destruct k; try easy.
simpl Vector.take; rewrite ?Vector_to_list_cons.
simpl; now rewrite IHtl.
Qed.

End Take.

End Type_agnostic.

Section Matrix_transposition.

Variable X : Type.
Notation vec := (Vector.t X).

(* Convert from a list of collumn vectors to a vector of row lists. *)
Fixpoint transpose {n} (mat : list (vec n)) : Vector.t (list X) n :=
  match mat with
  | []     => Vector.const [] n
  | v :: m => Vector.map2 cons v (transpose m)
  end.

Lemma transpose_nil (mat : list (vec 0)) :
  transpose mat = ⟨⟩.
Proof.
induction mat; simpl. easy.
rewrite IHmat; apply Vector.case0 with (v:=a). easy.
Qed.

Theorem transpose_cons {n} (mat : list (vec (S n))) :
  transpose mat = map Vector.hd mat ;; transpose (map Vector.tl mat).
Proof.
induction mat; simpl. easy.
apply Vector.caseS' with (v:=a).
intros; now rewrite IHmat.
Qed.

Theorem transpose_nth {n} (mat : list (vec n)) (i : Fin.t n)  :
  Vector.nth (transpose mat) i = map (λ v, Vector.nth v i) mat.
Proof.
induction mat; simpl. apply Vector.const_nth.
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
