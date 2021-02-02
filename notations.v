(* General purpose notations. *)

Require Vector.
Require Import Utf8 List.

(* Sigma types. *)
Notation "'Σ' x .. y , P" := (sigT (λ x, .. (sigT (λ y, P)) ..))
  (at level 200, x binder, y binder, right associativity,
  format "'[ ' '[ ' Σ  x .. y ']' ,  '/' P ']'") : type_scope.

(* Cartesian products. *)
Notation "A × B" := (prod A B) (at level 100).

(* List inclusions. *)
(* Notation "a ⊆ b" := (∀x, In x a -> In x b) (at level 50). *)
(* Notation "a == b" := (∀x, In x a <-> In x b) (at level 50). *)

(* Boolean vectors. *)
Notation vec := (Vector.t bool).
