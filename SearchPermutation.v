
(* ################################################################# *)
(** * Search and Permutations

    CS 472 check-in starter.
    Zuhaib Ilyas & Sufiyan Shariff
    Partially used AI to help with proof, where stuck *)

From Stdlib Require Import Arith List Permutation.

(* ################################################################# *)
(** * Linear Search *)

Fixpoint linear_search (e : nat) (l : list nat) : bool :=
  match l with
  | nil => false
  | x :: xs => if Nat.eqb e x then true else linear_search e xs
  end.

Lemma linear_search_cons (e a : nat) (xs : list nat) :
  linear_search e (a :: xs) = if Nat.eqb e a then true else linear_search e xs.
Proof. reflexivity. Qed.


Lemma linear_search_true_iff_In :
  forall (e : nat) (l : list nat), linear_search e l = true <-> In e l.
Proof.
  intros e l; split.
  - revert e; induction l as [|a xs IH]; simpl.
    + discriminate.
    + intros e H; destruct (Nat.eqb_spec e a) as [Heq | Hne].
      * subst; left; reflexivity.
      * right; now apply IH.
  - intros Hin; induction l as [|a xs IH].
    + contradiction.
    + destruct Hin as [Heq | Hin'].
      * subst; rewrite linear_search_cons, Nat.eqb_refl; reflexivity.
      * rewrite linear_search_cons; destruct (Nat.eqb e a); simpl;
          [ reflexivity | now apply IH ].
Qed.

Theorem search_correct_on_permutations :
  forall (l l_perm : list nat) (e : nat),
    Permutation l l_perm ->
    (linear_search e l = true <-> linear_search e l_perm = true).
Proof.
  intros l l_perm e Hperm.
  rewrite !linear_search_true_iff_In.
  split.
  - apply Permutation_in; assumption.
  - intro Hin.
    apply Permutation_in with (l := l_perm) (l' := l); [| assumption].
    now apply Permutation_sym.
Qed.
