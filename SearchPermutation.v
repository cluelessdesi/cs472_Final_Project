
(* ################################################################# *)
(** Search and Permutations

    CS 472 SP'26 Final Project.
    Zuhaib Ilyas & Sufiyan Shariff
    
    Sources Used / Citations:
      Partially used AI to help with proof, where stuck (clarify as per profs request)
      insert, sort functions: https://coq.vercel.app/ext/sf/vfa/full/Sort.html
      Sorted Predicate, proofs for check_inserting_into_sorted & sorting_lists_works: https://gist.github.com/siraben/3fedfc2c5a242136a9bc6725064e9b7d
      Claude provided suggestion to use max_calls as a decreasing value that binary_search could use.
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
  sfirstorder use: check_inserting_into_sorted.
Qed.

(* index access function
   - goes through list till it finds element at index N
   - N is midpoint of low and high
   - idx starts at low, need to pass a sublist starting at low for this to work, did not use approach
   - idx starts at 0
*)

Fixpoint index_access (mid : nat) (idx : nat) (l : list nat) : nat :=
  match l with
  | [] => 0
  | hd::tail =>
      if idx =? mid then hd
      else index_access mid (idx + 1) tail
  end.

(* creates a sublist starting from low
   equivalent to sub = list[low:] in python
   - did not use function
*)
Fixpoint create_sublist (start_here : nat) (idx : nat) (l : list nat) : list nat :=
  match l with
  | [] => []
  | hd::tail =>
      if idx <? start_here then create_sublist start_here (idx + 1) tail
      else hd :: create_sublist start_here (idx + 1) tail
  end.

(* binary search function
  - recursively halves the list looking for an element in given list (sorted) 
  - rocq error: cannot guess decreasing argument to fix => added a max_calls (suggestion provided by Claude)
*)
Fixpoint binary_search (e low high max_calls : nat) (l : list nat) : bool :=
  match max_calls with
  | 0 => false
  | S max_calls' =>
      if high <? low then false
      else
        let midpoint := ((high + low)/2) in
        (* complicated and more comp cost cos need to construct sublist on every iteration and we don't use it *)
        (* let item := index_access (midpoint - low) 0 (create_sublist low 0 l) in *)
        let item := index_access midpoint 0 l in
        if e =? item then true 
        else if e <? item then binary_search e low (midpoint - 1) max_calls' l
        else binary_search e (midpoint + 1) high max_calls' l
  end.

(* size function, gets length of list *)
Fixpoint sz (n : nat) (l : list nat) : nat :=
  match l with
  | [] => n 
  | hd::tail => sz (n+1) tail
  end.

(* call the binary search function with a sorted list
   - e: element we are trying to find
   - low: starts at 0
   - high: length of list - 1
   - max_calls: should ideally be log2(length of list), I set it to length of list
   - l: non empty sorted list
*)
Definition binary_search_caller (e : nat) (l : list nat) : bool :=
  match l with 
  | [] => false
  | _ => binary_search e 0 ((sz 0 l) - 1) (sz 0 l) (sort l)
  end.

(* proof binary search is correct *)

(* proof that using linear search and binary search return the same value: T/F for an element E *)
