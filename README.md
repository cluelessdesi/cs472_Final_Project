# CS 472 Final Project
This is the repository for the final project for CS 472, SP ' 26 semester <br/>
The project overview, implementation details and goals are described in the final project report. <br />
Brief information about our implementation is also provided below. <br />

## Instructors
- Professor: William Mansky
- TA: Eli Whitehouse

## Team
- Zuhaib Ilyas
- Sufiyan Shariff

# To run this project:
- Need to have Coq/Rocq installed (https://rocq-prover.org/releases/2025.01.0)
- Once you have installed Coq/Rocq, you need to install coq-hammer
- `opam repo add coq-released https://coq.inria.fr/opam/released` 
- `opam install coq-hammer`

## Our implemention:

# Linear Search
- Implemented linear_search : nat -> list nat -> bool , it scans left-to-right and returns true if the element is found.

# Proof: Linear Search Correctness
- Proved:
  - `linear_search_true_iff_In`(`linear_search e l = true <-> In e l`)
- Proof uses induction on the list and forward/backward directions of `<->`.

# Proof: Permutation 
- Proved:
  - `search_correct_on_permutations`
- Meaning: if `l_perm` is a permutation of `l`, then linear search gives the same boolean result on both lists.

# Insertion Sort:
- Implemented insertion sort using 2 functions: `insert` & `sort`.
- Binary search only works when the list is sorted, hence we need insertion sort (other sorting functions like selection, merge etc would also work).
- We also proved the correctness of insertion sort using the `Sorted` predicate in the proofs for: `checking_inserting_into_sorted` & `sorting_list_works`.

# Binary Search:
- Implemented `binary_search` function using recursion. The function is called on a sorted list with a `max_calls` which is maximum number of calls the function call should complete in.
- Apart from insertion sort, we also needed to implement a helper `index_access` function, which retrieves the item at the midpoint index to see if we have found our element.
- We also implement our own length function `sz` so we know the highest index we can find our element at. (This function was likely unnecessary, I just implemented it out of habit)
