(* A basic implementation of left-leaning red-black trees. *)
(* See: https://mew.org/~kazu/proj/red-black-tree/ *)

Require Import Lia.
From larith Require Import A_setup B1_utils C1_order.

Section Red_black_tree.

Variable X : Type.
Variable cmp : X -> X -> comparison.
Hypothesis ord : Order cmp.

Inductive rb_color := Red | Black.
Inductive rb_tree :=
  | Leaf
  | Fork (c : rb_color) (l : rb_tree) (x : X) (r : rb_tree).

Notation Rd := (Fork Red).
Notation Bk := (Fork Black).

Definition rb_balance_l c l z r :=
  match c, l with
  (* Rotation for double red fork. *)
  | Black, Rd (Rd xl x xr) y yr =>
    Rd (Bk xl x xr) y (Bk yr z r)
  (* No rotation needed. *)
  | _, _ => Fork c l z r
  end.

Definition rb_balance_r c l y r :=
  match c, l, r with
  (* Propagate red fork upward. *)
  | Black, Rd xl x xr, Rd zl z zr =>
    Rd (Bk xl x xr) y (Bk zl z zr)
  (* Rotation to make tree left-leaning. *)
  | _, _, Rd zl z zr =>
    Fork c (Rd l y zl) z zr
  (* No rotation needed. *)
  | _, _, _ => Fork c l y r
  end.

Fixpoint rb_ins x t :=
  match t with
  | Leaf => Rd Leaf x Leaf
  | Fork c l y r =>
    match cmp x y with
    | Eq => t
    | Lt => rb_balance_l c (rb_ins x l) y r
    | Gt => rb_balance_r c l y (rb_ins x r)
    end
  end.

Definition rb_insert x t :=
  match rb_ins x t with
  | Fork _ l x r => Bk l x r
  | Leaf => Leaf (* never reached. *)
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

(* Prove that the algorithm obeys the invariants that keep the tree balanced. *)
Section Tree_invariants.

(* A red node has two black children; there are no red nodes on the right. *)
Fixpoint LLRB_col c t :=
  match c, t with
  | _, Leaf => True
  | Black, Bk l _ r =>  (LLRB_col Red l \/ LLRB_col Black l) /\ LLRB_col Black r
  | Red, Rd l _ r => LLRB_col Black l /\ LLRB_col Black r
  | _, _ => False
  end.

(* The root is red and its left child is as well. *)
Notation Quasi_LLRB_col t :=
  match t with
  | Rd l _ r => LLRB_col Red l /\ LLRB_col Black r
  | _ => False
  end.

Inductive Bk_balanced : nat -> rb_tree -> Prop :=
  | Bk_balanced_Leaf :
    Bk_balanced 0 Leaf
  | Bk_balanced_Rd n l x r :
    Bk_balanced n l -> Bk_balanced n r -> Bk_balanced n (Rd l x r)
  | Bk_balanced_Bk n l x r :
    Bk_balanced n l -> Bk_balanced n r -> Bk_balanced (S n) (Bk l x r).

Definition LLRB p n t := LLRB_col p t /\ Bk_balanced n t.
Definition Quasi_LLRB n t := Quasi_LLRB_col t /\ Bk_balanced n t.

Theorem rb_max_height n t :
  Bk_balanced n t -> rb_height t <= 2 * n.
Proof.
revert n; induction t; simpl; intros; inv H; auto.
all: apply IHt1 in H3; apply IHt2 in H6; lia.
Qed.

Theorem LLRB_rb_insert n x t :
  LLRB Black n t ->
  LLRB Black n (rb_insert x t) \/
  LLRB Black (S n) (rb_insert x t).
Proof.
Admitted.

End Tree_invariants.

(* Prove that the algorithm maintains a binary-search tree structure. *)
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
