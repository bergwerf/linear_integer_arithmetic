(* General purpose notations. *)

Require Import Utf8 Vector.

(* Sigma types. *)
Notation "'Σ' x .. y , P" := (sigT (λ x, .. (sigT (λ y, P)) ..))
  (at level 200, x binder, y binder, right associativity,
  format "'[ ' '[ ' Σ  x .. y ']' ,  '/' P ']'") : type_scope.

(* Cartesian products. *)
Notation "A × B" := (prod A B) (at level 100).

(* We primarily use boolean vectors. *)
Notation vec := (Vector.t bool).
