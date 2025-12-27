module TSP where

open import Data.Nat
open import Data.Bool
open import Data.List
open import Data.Product
open import Relation.Binary.PropositionalEquality

-- A simple representation of nodes as Fin n
record Graph (n : ℕ) : Set where
  field
    costs : (i j : ℕ) → i < n → j < n → ℕ

-- A tour is a permutation of nodes
record Tour {n : ℕ} (g : Graph n) : Set where
  field
    path : List ℕ
    length-is-n : length path ≡ n
    is-permutation : Set -- Simplified for this model

-- MTZ Subtour Elimination Condition
-- u_i - u_j + n * x_ij ≤ n - 1
-- This ensures that there are no cycles that don't pass through node 0.
record MTZConstraint (n : ℕ) : Set where
  field
    x : (i j : ℕ) → i < n → j < n → Bool -- Edge variables
    u : (i : ℕ) → i < n → ℕ               -- Auxiliary variables
    
    node-zero : (i : ℕ) → (p : i < n) → u i p ≡ 0 -- Node 0 is the start
    
    subtour-elim : ∀ {i j} (pi : i < n) (pj : j < n) → 
      i ≢ 0 → j ≢ 0 → i ≢ j → 
      (if x i j pi pj then u i pi + 1 ≤ u j pj else ⊤) -- Simplified MTZ

-- The Gavish-Graves (GG) formulation uses flow variables:
-- y_ij is the flow on edge (i,j)
-- Node j (j > 0) consumes 1 unit of flow
record GGConstraint (n : ℕ) : Set where
  field
    x : (i j : ℕ) → i < n → j < n → Bool
    y : (i j : ℕ) → i < n → j < n → ℕ -- Flow variables
    
    flow-edge : ∀ {i j} (pi : i < n) (pj : j < n) → 
      (if x i j pi pj then y i j pi pj ≤ (n - 1) else y i j pi pj ≡ 0)
    
    node-balance : ∀ {j} (pj : j < n) → j ≢ 0 →
      (sum-in : ℕ) → (sum-out : ℕ) →
      sum-in ≡ sum-out + 1 

-- Preprocessing: Naive fixing based on raw cost
-- DOES NOT WORK (Unsound)
-- Counter-example: An edge (i,j) might be expensive (1001) but necessary for the 
-- optimal tour if all other edges are extremely cheap (e.g. 1).
-- Fixing it to zero would lose the optimal solution.
NaiveFixing : ∀ {n} → Graph n → (i j : ℕ) → i < n → j < n → Bool
NaiveFixing g i j pi pj = (g.costs i j pi pj ) > 1001 

-- Sound Preprocessing: Reduced Cost Fixing
-- If the lower bound of a problem fixed with edge (i,j) exceeds a known upper bound,
-- then the edge (i,j) cannot be part of any optimal solution.
record ReducedCostFixing {n : ℕ} (g : Graph n) : Set where
  field
    LB : ℕ -- Global lower bound (e.g. from Assignment Problem)
    UB : ℕ -- Best known upper bound (from a heuristic)
    rc : ℕ -- Reduced cost of edge (i,j)
    
    fixing-condition : (LB + rc) > UB
    
    -- Soundness Proof:
    -- Any tour T containing (i,j) must have cost(T) ≥ LB + rc.
    -- Since LB + rc > UB, and UB ≥ cost(OptimalTour),
    -- then cost(T) > cost(OptimalTour), so T is not optimal.
    soundness : ∀ (T : Tour g) → (i j : ℕ) → (pi : i < n) → (pj : j < n) →
                (if T.path contains (i , j) then True else False) -- Simplified
                → cost T > cost (OptimalTour g)
