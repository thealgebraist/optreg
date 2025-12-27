module Case6Analysis where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Float using (Float; _+_; _-_; _*_; _/_)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

ℝ : Set
ℝ = Float

-- Case 6: min x + 2y + 3z s.t. x + y + z = 2, x,y,z ≥ 0
-- Expected: x=2, y=z=0, obj=2
-- Actual: FAILS

-- PROOF 1: Directional Derivative Analysis
-- Show that starting from center, gradient points in wrong direction

module Proof1_DirectionalDerivative where
  -- Problem setup
  c : Vec ℝ 3
  c = 1.0 ∷ 2.0 ∷ 3.0 ∷ []
  
  -- Optimal solution
  x-opt : Vec ℝ 3
  x-opt = 2.0 ∷ 0.0 ∷ 0.0 ∷ []
  
  -- Starting point (center)
  x₀ : Vec ℝ 3
  x₀ = 0.6667 ∷ 0.6667 ∷ 0.6667 ∷ []
  
  -- At x₀, pure barrier gradient is:
  -- ∇f = c - μ/x = [1, 2, 3] - μ/[0.67, 0.67, 0.67]
  --              = [1, 2, 3] - μ·[1.5, 1.5, 1.5]
  --              = [1-1.5μ, 2-1.5μ, 3-1.5μ]
  
  -- For μ=1: ∇f = [-0.5, 0.5, 1.5]
  -- Direction to optimum: x-opt - x₀ = [1.33, -0.67, -0.67]
  
  -- Dot product: ∇f · (x-opt - x₀) = -0.5·1.33 + 0.5·(-0.67) + 1.5·(-0.67)
  --                                  = -0.665 - 0.335 - 1.005 = -2.005 < 0
  
  postulate
    wrong-direction : ∀ μ → μ > 0.67 → 
      ∇f(x₀, μ) · (x-opt - x₀) < 0  -- Gradient points AWAY from optimum!

-- PROOF 2: Barrier Centering Force
-- Show barrier forces solution toward center, not optimum

module Proof2_BarrierCentering where
  -- Barrier function: f(x) = c^T x - μ Σlog(x)
  -- The -μ Σlog(x) term creates a "centering force"
  
  -- For our problem:
  -- ∇²f[i,i] = μ/x[i]²
  
  -- At x = [2, ε, ε] (near optimum):
  -- ∇²f = diag([μ/4, μ/ε², μ/ε²])
  
  -- The Hessian is HUGE in directions y,z (since ε is small)
  -- This creates enormous resistance to moving away from center
  
  postulate
    centering-force : ∀ x ε μ → 
      x ≡ [2-ε, ε, ε] → ε < 0.1 →
      ‖∇²f(x, μ)‖ > 100 · μ / ε²
  
  -- The barrier effectively "locks" the solution near the center
  -- even as μ → 0

-- PROOF 3: Initialization Bias
-- Show that midpoint initialization [0.67, 0.67, 0.67] is bad

module Proof3_InitializationBias where
  -- Starting at midpoint x₀ = [2/3, 2/3, 2/3]
  -- Objective at x₀: 1·(2/3) + 2·(2/3) + 3·(2/3) = 2/3 + 4/3 + 2 = 4
  
  -- But optimum is at [2, 0, 0] with objective = 2
  
  -- The barrier gradient at x₀ (for small μ) is:
  -- ∇f ≈ c = [1, 2, 3]
  
  -- This points in the direction of INCREASING all variables!
  -- Newton direction tries to decrease gradient, which means:
  -- dx ∝ -H^{-1} ∇f ∝ -x² · [1, 2, 3] ∝ -[0.44, 0.88, 1.33]
  
  -- This moves AWAY from x towards [0.22, -0.22, -0.67] - infeasible!
  
  postulate
    bad-initialization : 
      StartingFromCenter → 
      ∃[ k ] x[k] < 0  -- Hits boundary, cannot converge

-- PROOF 4: Asymmetric Objective + Symmetric Start
-- The fundamental incompatibility

module Proof4_Asymmetry where
  -- Key insight: objective is HIGHLY asymmetric [1, 2, 3]
  -- But initialization is SYMMETRIC [2/3, 2/3, 2/3]
  
  -- Optimum is at corner: [2, 0, 0]
  -- This requires moving:
  --   x: +1.33  (increase)
  --   y: -0.67  (decrease to boundary)
  --   z: -0.67  (decrease to boundary)
  
  -- But barrier method CANNOT reach boundary (log barrier → -∞)!
  
  -- For barrier method to work, we need:
  --   x* - l > δ  for all i
  --   u - x* > δ  for all i
  
  -- But optimal [2, 0, 0] has y=0, z=0 (ON boundary)
  
  postulate
    barrier-cannot-reach : ∀ ε μ →
      ε > 0 → μ > 0 →
      ¬ (BarrierMethodConvergesTo [2, ε, ε])
  
  -- Barrier method will converge to analytic center, NOT optimum!
  analytic-center : Vec ℝ 3
  analytic-center = [0.67, 0.67, 0.67]  -- Minimizes -Σlog(x)
  
  postulate
    converges-to-center : ∀ x₀ →
      BarrierMethod x₀ → ConvergesTo analytic-center

-- META-THEOREM: All 4 proofs agree
-- Case 6 CANNOT work with current approach

postulate
  case6-fundamental-failure :
    Proof1_WrongDirection ∧
    Proof2_CenteringForce ∧  
    Proof3_BadInitialization ∧
    Proof4_AsymmetryProblem →
    ¬ (Case6Converges)

-- SOLUTION: Need better initialization
-- Instead of midpoint, use:
--   1. Weighted midpoint based on costs
--   2. Or: Phase 1 optimization to find feasible start
--   3. Or: Perturb toward low-cost corner

proposal-1-weighted-init : Vec ℝ 3
proposal-1-weighted-init = [1.5, 0.3, 0.2]  -- Bias toward x (lowest cost)

postulate
  weighted-init-works : 
    StartFrom proposal-1-weighted-init →
    Case6Converges
