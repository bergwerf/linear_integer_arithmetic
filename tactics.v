(* Some general purpose tactics. *)

Require Import Bool PeanoNat Lia.

Ltac inv H := inversion H; subst; clear H.

Ltac bool_to_Prop :=
  match goal with
  | [H : _ && _ = true |- _] =>  apply andb_prop in H; destruct H
  | [H : _ || _ = true |- _]  => apply orb_true_elim in H; destruct H
  | [H : _ || _ = false |- _]  => apply orb_false_elim in H; destruct H
  | [H : _ =? _ = true |- _]   => apply Nat.eqb_eq in H
  | [H : _ =? _ = false |- _]  => apply Nat.eqb_neq in H
  | [H : _ <=? _ = true |- _]  => apply Nat.leb_le in H
  | [H : _ <=? _ = false |- _] => apply Nat.leb_gt in H
  | [H : _ <? _ = true |- _]   => apply Nat.ltb_lt in H
  | [H : _ <? _ = false |- _]  => apply Nat.ltb_ge in H
  | |- (_ && _ = true)   => apply andb_true_intro; split
  | |- (_ || _ = false)  => apply orb_false_intro
  | |- (_ || _ = true)   => apply orb_true_intro
  | |- (_ =? _ = true)   => apply Nat.eqb_eq
  | |- (_ =? _ = false)  => apply Nat.eqb_neq
  | |- (_ <=? _ = true)  => apply Nat.leb_le
  | |- (_ <=? _ = false) => apply Nat.leb_gt
  | |- (_ <? _ = true)   => apply Nat.ltb_lt
  | |- (_ <? _ = false)  => apply Nat.ltb_ge
  | _ => idtac
  end.

Ltac b_Prop := repeat bool_to_Prop.
Ltac b_lia := b_Prop; try (symmetry; b_Prop); lia.
