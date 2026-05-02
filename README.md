# cs472_Final_Project
Final Project for CS 472, SP ' 26 <br/>
Link to google doc: https://docs.google.com/document/d/1yNDm_zXJspuRbueUIACct1RGBbmFzgd9PUse1lPgu3I/edit?usp=sharing

## Team
- Zuhaib Ilyas
- Sufiyan Shariff

## Our implementions:

#  Linear Search
- Implemented linear_search : nat -> list nat -> bool , it scans left-to-right and returns true if the element is found.

# Proof: Linear Search Correctness
- Proved:
  - `linear_search_true_iff_In`(`linear_search e l = true <-> In e l`)
- Proof uses induction on the list and forward/backward directions of `<->`.

# Proof: Permutation 
- Proved:
  - `search_correct_on_permutations`
- Meaning: if `l_perm` is a permutation of `l`, then linear search gives the same boolean result on both lists.
