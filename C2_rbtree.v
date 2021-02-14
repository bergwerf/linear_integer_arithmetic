(* An implementation of the left-leaning red-black trees without deletion. *)
(* See: https://mew.org/~kazu/proj/red-black-tree/ *)

From larith Require Import A_setup B1_utils C1_order.

Section Red_black_tree.

Variable X : Type.
Variable cmp : X -> X -> comparison.
Hypothesis ord : Order cmp.

Inductive rb_color := Rd | Bk.
Inductive rb_tree :=
  | Leaf
  | Fork (c : rb_color) (l : rb_tree) (x : X) (r : rb_tree).

Definition rb_balance_l c l z r :=
  match l with
  (* Rotation for double red fork. *)
  | Fork Rd (Fork Rd xl x xr) y yr =>
    Fork Bk (Fork Bk xl x xr) y (Fork Bk yr z r)
  (* No rotation needed. *)
  | _ => Fork c l z r
  end.

Definition rb_balance_r c l y r :=
  match c, l, r with
  (* Propagate red fork upward. *)
  | Bk, Fork Rd xl x xr, Fork Rd zl z zr =>
    Fork Rd (Fork Bk xl x xr) y (Fork Bk zl z zr)
  (* Rotation to make tree left-leaning. *)
  | _, _, Fork Rd zl z zr =>
    Fork c (Fork Rd l y zl) z zr
  (* No rotation needed. *)
  | _, _, _ => Fork c l y r
  end.

Fixpoint rb_insert x t :=
  match t with
  | Leaf => Fork Rd Leaf x Leaf
  | Fork c l y r =>
    match cmp x y with
    | Eq => t
    | Lt => rb_balance_l c (rb_insert x l) y r
    | Gt => rb_balance_r c l y (rb_insert x r)
    end
  end.

Fixpoint rb_contains x t :=
  match t with
  | Leaf => false
  | Fork _ l y r =>
    match cmp x y with
    | Eq => true
    | Lt => rb_contains x l
    | Gt => rb_contains x r
    end
  end.

End Red_black_tree.
