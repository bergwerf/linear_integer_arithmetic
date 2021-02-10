(* A merge-sort + de-duplication implementation. *)

Require Import Utf8 List.
From larith Require Import tactics notations utilities.
Import ListNotations.

Notation Sorted cmp := (RTC (λ x y, cmp x y = Lt)).

Section Merge_sort.

Variable X : Type.
Variable cmp : X -> X -> comparison.
Notation Sorted := (Sorted cmp).

Fixpoint merge l1 l2 :=
  let fix merge_aux l2 :=
  match l1, l2 with
  | [], _ => l2
  | _, [] => l1
  | x1 :: l1', x2 :: l2' =>
    match cmp x1 x2 with
    | Eq => x1 :: merge l1' l2'
    | Lt => x1 :: merge l1' l2
    | Gt => x2 :: merge_aux l2'
    end
  end
  in merge_aux l2.

Fixpoint merge_cycle parts :=
  match parts with
  | []  => []
  | [l] => [l]
  | l1 :: l2 :: parts' => merge l1 l2 :: merge_cycle parts'
  end.

Fixpoint merge_sort n parts :=
  match n with
  | 0 => []
  | S m =>
    match merge_cycle parts with
    | [] => []
    | [l] => l
    | parts' => merge_sort m parts'
    end
  end.

Definition sort l := merge_sort (length l) (map (λ x, [x]) l).

Theorem merge_Sorted l1 l2 :
  Sorted l1 -> Sorted l2 -> Sorted (merge l1 l2).
Proof.
Admitted.

Theorem merge_NoDup l1 l2 :
  Sorted l1 -> Sorted l2 -> NoDup (merge l1 l2).
Proof.
Admitted.

Theorem merge_cycle_Sorted ls :
  Forall Sorted ls -> Forall Sorted (merge_cycle ls).
Proof.
Admitted.

Theorem merge_cycle_reduce ls :
  length ls > 1 -> length (merge_cycle ls) < length ls.
Proof.
Admitted.

Theorem sort_Sorted l :
  Sorted (sort l).
Proof.
Admitted.

Theorem sort_NoDup l :
  NoDup (sort l).
Proof.
Admitted.

Theorem sort_fixed_point l :
  sort (sort l) = sort l.
Proof.
Admitted.

End Merge_sort.

Arguments sort {_}.
