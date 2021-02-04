(* General purpose notations. *)

Require Vector.
Require Import Utf8 List.

(* Sigma types. *)
Notation "'Σ' x .. y , P" := (sigT (λ x, .. (sigT (λ y, P)) ..))
  (at level 200, x binder, y binder, right associativity,
  format "'[ ' '[ ' Σ  x .. y ']' ,  '/' P ']'") : type_scope.

(* Functions on nat without importing the proofs *)
Notation min := (Nat.min).
Notation max := (Nat.max).

(* Cartesian products. *)
Notation "A × B" := (prod A B) (at level 100).

(* Boolean vectors. *)
Notation vec := (Vector.t bool).
