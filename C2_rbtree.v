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

Definition rb_col t :=
  match t with
  | Leaf => Black
  | Fork c _ _ _ => c
  end.

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
  | Fork _ l _ r => S (max (rb_height l) (rb_height r))
  end.

(* Prove that the algorithm obeys the invariants that keep the tree balanced. *)
Section Tree_invariants.

(* A red node has two black children; there are no red nodes on the right. *)
Fixpoint LLRB_col c t :=
  match c, t with
  | _, Leaf => True
  | Black, Bk l _ r => LLRB_col (rb_col l) l /\ LLRB_col Black r
  | Red, Rd l _ r => LLRB_col Black l /\ LLRB_col Black r
  | _, _ => False
  end.

(* The root is red and its left child is as well. *)
Notation Quasi_LLRB_col t :=
  match t with
  | Rd l _ r => LLRB_col Red l /\ LLRB_col Black r
  | _ => False
  end.

(* The black nodes are equally balanced. *)
Inductive Bk_balanced : nat -> rb_tree -> Prop :=
  | Bk_balanced_Leaf :
    Bk_balanced 0 Leaf
  | Bk_balanced_Rd n l x r :
    Bk_balanced n l -> Bk_balanced n r -> Bk_balanced n (Rd l x r)
  | Bk_balanced_Bk n l x r :
    Bk_balanced n l -> Bk_balanced n r -> Bk_balanced (S n) (Bk l x r).

Definition LLRB p n t := LLRB_col p t /\ Bk_balanced n t.
Definition Quasi_LLRB n t := Quasi_LLRB_col t /\ Bk_balanced n t.

Lemma LLRB_Rd_inv c n l x r :
  LLRB Red n (Fork c l x r) -> LLRB Black n l /\ LLRB Black n r.
Proof.
intros []. inv H0; simpl in H. easy.
Qed.

Lemma LLRB_0_Bk_inv c l x r :
  ¬LLRB Black 0 (Fork c l x r).
Proof.
intros []; inv H0.
Qed.

Lemma LLRB_rb_col_Black t :
  LLRB_col Black t -> rb_col t = Black.
Proof.
destruct t. easy.
destruct c; easy.
Qed.

Lemma LLRB_Bk_inv c n l x r :
  LLRB Black (S n) (Fork c l x r) ->
  LLRB (rb_col l) n l /\ LLRB (rb_col r) n r.
Proof.
intros []. inv H0. simpl in H.
repeat split; try easy.
rewrite LLRB_rb_col_Black; easy.
Qed.

Theorem rb_height_bound_any_root c n t :
  LLRB c n t ->
  match c with
  | Red => rb_height t <= 1 + 2 * n
  | Black => rb_height t <= 2 * n
  end.
Proof.
revert n c; induction t; simpl; intros.
- destruct c, H; inv H0; simpl; auto.
- destruct c0.
  + apply LLRB_Rd_inv in H as [].
    apply IHt1 in H; apply IHt2 in H0; lia.
  + destruct n. apply LLRB_0_Bk_inv in H; easy.
    apply LLRB_Bk_inv in H as [].
    apply IHt1 in H; apply IHt2 in H0.
    destruct (rb_col t1), (rb_col t2); lia.
Qed.

Corollary rb_height_bound n t :
  LLRB Black n t -> rb_height t <= 2 * n.
Proof.
intros; apply rb_height_bound_any_root in H; easy.
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
  In_interval upb lwb x -> BST lwb upb t -> BST lwb upb (rb_insert x t).
Proof.
Admitted.

Theorem rb_insert_contains x t :
  rb_contains x (rb_insert x t) = true.
Proof.
Admitted.

End Correct_insertion.

End Red_black_tree.
