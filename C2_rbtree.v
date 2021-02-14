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

Fixpoint rb_height t :=
  match t with
  | Leaf => 0
  | Fork _ l _ r => max (rb_height l) (rb_height r)
  end.

Section Tree_invariants.

Fixpoint Rd_child Bk_root t :=
  match t with
  | Leaf => True
  | Fork Bk l _ r => Rd_child False l /\ Rd_child False r
  | Fork Rd l _ r => ¬Bk_root /\ Rd_child True l /\ Rd_child True r
  end.

Inductive Bk_height : nat -> rb_tree -> Prop :=
  | Bk_height_Leaf :
    Bk_height 0 Leaf
  | Bk_height_Rd n l x r :
    Bk_height n l -> Bk_height n r -> Bk_height n (Fork Rd l x r)
  | Bk_height_Bk n l x r :
    Bk_height n l -> Bk_height n r -> Bk_height (S n) (Fork Bk l x r).

Fixpoint Left_leaning t :=  
  match t with
  | Leaf => True
  | Fork Bk _ _ (Fork Rd _ _ _) => False
  | Fork _ l _ r => Left_leaning l /\ Left_leaning r
  end.

Definition LLRB n t :=
  Rd_child True t /\ Bk_height n t /\ Left_leaning t.

Theorem rb_max_height n t :
  LLRB n t -> rb_height t < 2 * n.
Proof.
Admitted.

Theorem rb_insert_LLRB n x t :
  LLRB n t -> LLRB n (rb_insert x t) \/ LLRB (S n) (rb_insert x t).
Proof.
Admitted.

End Tree_invariants.

Section Correct_insertion.

Definition In_interval lwb upb y :=
  match lwb with
  | Some x => cmp x y = Lt
  | None => True
  end /\
  match upb with
  | Some z => cmp y z = Lt
  | None => True
  end.

Fixpoint BST lwb upb t :=
  match t with
  | Leaf => True
  | Fork _ l y r =>
    BST lwb (Some y) l /\
    BST (Some y) upb r /\
    In_interval lwb upb y
  end.

Theorem rb_insert_BST upb lwb x t :
  BST lwb upb t -> BST lwb upb (rb_insert x t).
Proof.
Admitted.

Theorem rb_insert_contains x t :
  rb_contains x (rb_insert x t) = true.
Proof.
Admitted.

End Correct_insertion.

End Red_black_tree.
