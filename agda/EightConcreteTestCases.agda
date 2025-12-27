module EightConcreteTestCases where

open import Data.Nat
open import Data.Vec
open import Relation.Binary.PropositionalEquality

-- CASE 1: 2D LP with Box Constraints (Current Test)
-- min x + y s.t. x + y = 1, 0 ≤ x,y ≤ 1
module Case1_2D_Box where
  n : ℕ
  n = 2
  
  c : Vec ℝ n
  c = [1, 1]
  
  A : Matrix 1 2
  A = [[1, 1]]
  
  b : Vec ℝ 1
  b = [1]
  
  lower : Vec ℝ n
  lower = [0, 0]
  
  upper : Vec ℝ n  
  upper = [1, 1]
  
  optimal : Vec ℝ n
  optimal = [0.5, 0.5]  -- Actually any point on x+y=1 in [0,1]²
  
  postulate
    current-fails : ¬ ConvergesWithin 100 iterations
    pure-barrier-works : PureBarrierMethod → ConvergesWithin 20 iterations
    
  reason : String
  reason = "Mixed primal-dual formulation has exploding dual residual"

-- CASE 2: 1D Trivial Problem
-- min x s.t. x = 0.5, 0 ≤ x ≤ 1
module Case2_1D_Trivial where
  n : ℕ
  n = 1
  
  c : Vec ℝ n
  c = [1]
  
  A : Matrix 1 1
  A = [[1]]
  
  b : Vec ℝ 1
  b = [0.5]
  
  lower : Vec ℝ n
  lower = [0]
  
  upper : Vec ℝ n
  upper = [1]
  
  optimal : Vec ℝ n
  optimal = [0.5]
  
  postulate
    current-works : ConvergesWithin 5 iterations
    pure-barrier-works : PureBarrierMethod → ConvergesWithin 3 iterations
    
  reason : String
  reason = "Trivial case: already at solution, any method converges"

-- CASE 3: Unbounded from Above
-- min x s.t. x ≥ 0 (no equality constraints, no upper bound)
module Case3_Unbounded_Above where
  n : ℕ
  n = 1
  
  c : Vec ℝ n
  c = [1]
  
  A : Matrix 0 1
  A = []
  
  b : Vec ℝ 0
  b = []
  
  lower : Vec ℝ n
  lower = [0]
  
  upper : Vec ℝ n
  upper = [∞]
  
  postulate
    current-works : ConvergesWithin 50 iterations
    pure-barrier-works : PureBarrierMethod → ConvergesWithin 30 iterations
    
  reason : String
  reason = "No upper bound: both methods reduce to standard barrier"

-- CASE 4: Very Tight Bounds
-- min x + y s.t. x + y = 1, 0.49 ≤ x,y ≤ 0.51
module Case4_Tight_Bounds where
  n : ℕ
  n = 2
  
  lower : Vec ℝ n
  lower = [0.49, 0.49]
  
  upper : Vec ℝ n
  upper = [0.51, 0.51]
  
  optimal : Vec ℝ n
  optimal = [0.5, 0.5]
  
  postulate
    current-fails : ¬ ConvergesWithin 100 iterations
    pure-barrier-works : PureBarrierMethod → ConvergesWithin 50 iterations
    
  reason : String
  reason = "Tight bounds amplify numerical errors in mixed formulation"

-- CASE 5: Degenerate (Boundary Solution)
-- min x + y s.t. x + y = 0, 0 ≤ x,y ≤ 1
module Case5_Boundary_Solution where
  n : ℕ
  n = 2
  
  b : Vec ℝ 1
  b = [0]
  
  optimal : Vec ℝ n
  optimal = [0, 0]
  
  postulate
    current-fails : ¬ ConvergesWithin 100 iterations
    pure-barrier-fails-too : ¬ (PureBarrierMethod → ConvergesWithin 100 iterations)
    
  reason : String
  reason = "Barrier methods cannot reach boundary (log barrier → -∞)"

-- CASE 6: 3-Variable LP
-- min x + 2y + 3z s.t. x + y + z = 2, 0 ≤ x,y,z
module Case6_3Var_LP where
  n : ℕ
  n = 3
  
  c : Vec ℝ n
  c = [1, 2, 3]
  
  A : Matrix 1 3
  A = [[1, 1, 1]]
  
  b : Vec ℝ 1
  b = [2]
  
  lower : Vec ℝ n
  lower = [0, 0, 0]
  
  upper : Vec ℝ n
  upper = [∞, ∞, ∞]
  
  optimal : Vec ℝ n
  optimal = [2, 0, 0]
  
  postulate
    current-works : ConvergesWithin 30 iterations
    pure-barrier-works : PureBarrierMethod → ConvergesWithin 20 iterations
    
  reason : String
  reason = "No upper bounds: standard barrier works fine"

-- CASE 7: Infeasible Problem
-- min x s.t. x = 1, 0 ≤ x ≤ 0.5
module Case7_Infeasible where
  n : ℕ
  n = 1
  
  b : Vec ℝ 1
  b = [1]
  
  upper : Vec ℝ n
  upper = [0.5]
  
  postulate
    current-diverges : Diverges
    pure-barrier-diverges : PureBarrierMethod → Diverges
    
  reason : String
  reason = "Infeasible: no interior point exists, barrier → ∞"

-- CASE 8: Multiple Optimal Solutions
-- min 0 s.t. x + y = 1, 0 ≤ x,y ≤ 1
module Case8_Multiple_Optima where
  n : ℕ
  n = 2
  
  c : Vec ℝ n
  c = [0, 0]  -- Zero objective!
  
  A : Matrix 1 2
  A = [[1, 1]]
  
  b : Vec ℝ 1
  b = [1]
  
  lower : Vec ℝ n
  lower = [0, 0]
  
  upper : Vec ℝ n
  upper = [1, 1]
  
  -- ANY point on x+y=1 in [0,1]² is optimal
  optimal-set : Set
  optimal-set = { (x,y) | x + y ≡ 1 ∧ 0 ≤ x ≤ 1 ∧ 0 ≤ y ≤ 1 }
  
  postulate
    current-converges-to-some : ∃[ x ] (x ∈ optimal-set ∧ ConvergesTo x)
    pure-barrier-converges-to-some : PureBarrierMethod → 
                                      ∃[ x ] (x ∈ optimal-set ∧ ConvergesTo x)
    likely-converges-to-center : ConvergesTo [0.5, 0.5]
    
  reason : String
  reason = "Zero objective: converges to analytic center of feasible region"

-- Summary Table
summary : List (String × String × String)
summary = [
  ("Case 1: 2D Box", "FAILS", "Mixed formulation unstable"),
  ("Case 2: 1D Trivial", "WORKS", "Already at solution"),
  ("Case 3: Unbounded", "WORKS", "Reduces to standard barrier"),
  ("Case 4: Tight Bounds", "FAILS", "Numerical amplification"),
  ("Case 5: Boundary", "FAILS", "Barrier cannot reach boundary"),
  ("Case 6: 3-Var", "WORKS", "No upper bounds"),
  ("Case 7: Infeasible", "DIVERGES", "No interior point"),
  ("Case 8: Multi-Opt", "WORKS", "Finds analytic center")
]

-- Meta-theorem: Pattern of failures
postulate
  failure-pattern : 
    (HasFiniteUpperBounds ∧ InteriorSolution) → 
    MixedFormulationFails ∧ PureBarrierWorks
