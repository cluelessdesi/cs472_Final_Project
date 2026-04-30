
(* ################################################################# *)
(** Search and Permutations

    CS 472 SP'26 Final Project.
    Zuhaib Ilyas & Sufiyan Shariff
    
    Sources Used / Citations:
      Partially used AI to help with proof, where stuck (clarify as per profs request)
      insert, sort functions: https://coq.vercel.app/ext/sf/vfa/full/Sort.html
      Sorted Predicate, proofs for check_inserting_into_sorted & sorting_lists_works: https://gist.github.com/siraben/3fedfc2c5a242136a9bc6725064e9b7d
    
    add to README later:
      installed coq-hammer
*)

From Stdlib Require Import Arith List Permutation.
Import ListNotations.
From Hammer Require Import Tactics.

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

(* binary search *)
(* need to make sure list is sorted first *)

(* sorting
  - insertion sort: https://coq.vercel.app/ext/sf/vfa/full/Sort.html
*)

(* if list is empty, just make a singleton list with i
   else, determine the right position to insert i in 
*)
Fixpoint insert (i : nat) (l : list nat) :=
  match l with
  | [] => [i]
  | h :: t => if i <=? h then i :: h :: t else h :: insert i t
  end.

(* if list is empty, it's already sorted / nothing to sort
   else, insert current element of unsorted (given) list into a sorted list
*)
Fixpoint sort (l : list nat) : list nat :=
  match l with
  | [] => []
  | h :: t => insert h (sort t)
  end.

(* Sorted predicate: https://gist.github.com/siraben/3fedfc2c5a242136a9bc6725064e9b7d
   - helpful to prove sort and insert work correctly
   - if empty list, it's sorted
   - else if singleton, list with that one element is sorted
   - else, for n, m, p in list, if n is less than m, we can sort list with m & p, then list with n, m and p is sorted
*)
Inductive Sorted : list nat -> Prop :=
| sorted_nil : Sorted []
| sorted_singleton : forall n, Sorted [n]
| sorted_cons : forall n m p, n <= m -> Sorted (m :: p) -> Sorted (n :: m :: p).

(* proof insert and sort functions work
  - adding an element x to a sorted list should result in a sorted list
  - for any list l, sort l should result in a sorted list
*)

Lemma check_inserting_into_sorted:
  forall (x : nat) (l : list nat), Sorted l -> Sorted (insert x l).
Proof.
   induction l.
  - sfirstorder.
  - destruct l; sblast.
Qed.

Lemma sorting_lists_works:
  forall (l : list nat), Sorted (sort l).
Proof.
  induction l; 
  sfirstorder use: sorted_insert.
Qed.

(* index access function
   - goes through list till it finds element at index N
   - N is midpoint of low and high
   - idx starts at low
*)
Fixpoint index_access (mid : nat) (idx : nat) (l : list nat) : nat :=
  match idx with
  | mid => (* split l into hd::tail and return hd *)
  | _ => (* split l into hd::tail and call index_access with idx+1 *)
  end.

(* binary search function
  - recursively halves the list looking for an element in given list (sorted) 
*)
Fixpoint binary_search (e low high : nat) (l : list nat) : bool :=
  if high <? low then false
  else 
    let midpoint := ((high - low)/2).
    let item := index_access midpoint low l
    if item Nat.eqb e then true 
    else 
      if e <? item then binary_search e low (midpoint - 1) l
      else binary_search e (midpoint + 1) high l
  end.

(* call the binary search function with a sorted list *)
Definition binary_search_caller (e : nat) (l : list nat) :=
  binary_search e 0 (len l) (sort l).

(* proof binary search is correct *)

(* proof that using linear search and binary search return the same value: T/F for an element E *)
