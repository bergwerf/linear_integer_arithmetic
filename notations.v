(* General purpose notations. *)

Require Import Utf8 Vector.

(* Sigma types. *)
Notation "'Σ' x .. y , P" := (sigT (λ x, .. (sigT (λ y, P)) ..))
  (at level 200, x binder, y binder, right associativity,
  format "'[ ' '[ ' Σ  x .. y ']' ,  '/' P ']'") : type_scope.

(* Cartesian products. *)
Notation "A × B" := (prod A B) (at level 100).

(* Vectors. *)
Notation vec := (Vector.t bool).
Notation vnil := (Vector.nil _).
Notation vcons := (Vector.cons _).
Notation proj n := (λ v, Vector.nth v n).

Notation "⟨ ⟩" := (vnil) (format "⟨ ⟩").
Notation "h ;; t" := (vcons h _ t)
  (at level 60, right associativity, format "h  ;;  t").

Notation "⟨ x ⟩" := (x ;; ⟨⟩).
Notation "⟨ x ; y ; .. ; z ⟩" :=
  (vcons x _ (vcons y _ .. (vcons z _ (nil _)) ..)).
