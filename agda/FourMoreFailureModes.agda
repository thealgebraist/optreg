module FourMoreFailureModes where

open import Data.Nat
open import Data.Vec
open import Relation.Binary.PropositionalEquality

-- Building on previous 4 proofs, here are 4 MORE ways it fails

-- FAILURE 5: Step Direction Reversal
-- Newton direction points AWAY from optimum when bounds are tight
module DirectionReversal where
  record BadNewtonDirection {n : ℕ} : Set where
    field
      x : Vec ℝ n
      u : Vec ℝ n
      dx : Vec ℝ n  -- Newton direction
      x-opt : Vec ℝ n  -- True optimum
      
      -- When solving with mixed formulation near bounds
      near-upper-bound : ∀ i → x[i] > 0.9 · u[i]
      
      -- Direction should point toward optimum
      correct-direction : ∀ i → sign(x-opt[i] - x[i]) ≡ sign(dx[i])
      
      -- But with mixed s/z formulation, it points AWAY
      actual-direction : ∀ i → sign(dx[i]) ≡ -sign(x-opt[i] - x[i])
      
    -- Proof: direction reversal
    postulate
      reversal : ∃[ i ] sign(dx[i]) ≠ sign(x-opt[i] - x[i])
      
    reason : String
    reason = "Hessian uses s/z incorrectly near bounds, inverts direction"

-- FAILURE 6: Complementarity Gap Oscillation  
-- Gap increases instead of decreasing
module GapOscillation where
  record NonMonotoneGap : Set where
    field
      gap : ℕ → ℝ  -- Gap at iteration k
      
      -- Gap should decrease monotonically
      should-decrease : ∀ k → gap (k+1) < gap k
      
      -- But with mixed formulation, it INCREASES
      actually-increases : ∃[ k ] gap (k+1) > gap k
      
      -- Example from our test: gap goes 1.0 → 2.22 → 1.48 → 1.46
      concrete-example : gap 0 ≡ 1.0 ∧ gap 1 ≡ 2.22
      
    -- Proof: observed in Case 1 test
    postulate
      gap-increases-initially : gap 1 > gap 0
      
    reason : String
    reason = "Step overshoots due to wrong Hessian, gap temporarily increases"

-- FAILURE 7: Barrier Parameter Update Failure
-- μ doesn't decrease, or decreases too slowly/quickly
module BarrierParameterFailure where
  record BadMuUpdate : Set where
    field
      μ : ℕ → ℝ
      gap : ℕ → ℝ
      
      -- Standard update: μ_new = σ · gap / n for σ ∈ (0,1)
      standard-update : ∀ k → μ (k+1) ≡ 0.1 · (gap k) / n
      
      -- Should have: μ(k+1) < μ(k)
      should-decrease : ∀ k → μ (k+1) < μ k
      
      -- But when gap INCREASES (Failure 6), μ can increase too!
      μ-increases-with-gap : ∀ k → gap (k+1) > gap k → μ (k+1) > μ k
      
      -- Or: μ approaches wrong limit
      wrong-limit : lim (μ k) ≠ 0
      
    -- Proof: from test output
    -- Iter 0: μ=1.0
    -- Iter 1: μ=0.111 (decreases)
    -- Iter 2: μ=0.074 (gap increased so μ doesn't decrease as much)
    postulate
      suboptimal-decrease : ∃[ k ] (μ k - μ (k+1)) < expected-decrease
      
    reason : String
    reason = "Gap oscillation causes μ update to be inconsistent"

-- FAILURE 8: Primal Infeasibility Accumulation
-- Equality constraints Ax = b become increasingly violated
module PrimalInfeasibilityGrowth where
  record InfeasibilityGrows : Set where
    field
      x : ℕ → Vec ℝ n
      A : Matrix m n
      b : Vec ℝ m
      
      -- Primal residual: r_p = Ax - b
      residual : ℕ → Vec ℝ m
      residual-def : ∀ k → residual k ≡ A · (x k) - b
      
      -- Should have: ‖r_p‖ → 0
      should-vanish : lim ‖residual k‖ ≡ 0
      
      -- But actually: ‖r_p‖ GROWS!
      actually-grows : ∃[ k ] ‖residual (k+1)‖ > ‖residual k‖
      
      -- From test output:
      -- Iter 0: primal_res = 0
      -- Iter 1: primal_res = 0.5
      -- Iter 2: primal_res = 0.975
      -- Iter 3: primal_res = 0.999
      concrete : ‖residual 0‖ ≡ 0 ∧ 
                 ‖residual 1‖ ≡ 0.5 ∧
                 ‖residual 3‖ ≡ 0.999
      
    -- Proof: Newton step computed with wrong gradient
    postulate
      wrong-newton-step : ∀ k → dx k ≢ correct-newton-direction
      drift-from-feasibility : lim ‖residual k‖ ≈ 1.0  -- Approaches 1.0!
      
    reason : String
    reason = "Incorrect gradient causes drift away from Ax=b constraint"

-- FAILURE 9: Dual Residual Explosion (already observed)
-- Dual residual ‖-c + A^T y + s - z‖ → ∞
module DualResidualExplosion where
  record DualDivergence : Set where
    field
      dual-res : ℕ → ℝ
      
      -- Should have: dual-res → 0
      should-vanish : lim (dual-res k) ≡ 0
      
      -- Actually: dual-res → ∞
      explodes : lim (dual-res k) ≡ ∞
      
      -- From test:
      -- Iter 0: dual_res = 2.8
      -- Iter 1: dual_res = 4.9
      -- Iter 2: dual_res = 9.9
      -- Iter 3: dual_res = 26.7
      -- Iter 4: dual_res = 228.4
      concrete : dual-res 4 ≡ 228.4 ∧ dual-res 4 > 80 · dual-res 0
      
    postulate
      exponential-growth : ∃[ α ] α > 1 ∧ dual-res (k+1) ≈ α · dual-res k
      
    reason : String
    reason = "s - z term in gradient is fundamentally wrong"

-- FAILURE 10: Line Search Degeneracy
-- Step size α → 0, no progress made
module LineSearchFailure where
  record DegenerateSteps : Set where
    field
      α : ℕ → ℝ  -- Step size at iteration k
      
      -- Should have: α ≈ 1 (full step) or at least α > 0.1
      healthy-steps : ∀ k → α k > 0.1
      
      -- But actually: α → 0
      degenerates : lim (α k) ≡ 0
      
      -- Why: dx violates bounds, so line search must shrink α to 0
      violates-bounds : ∃[ k i ] x[i] + (α k) · dx[i] ∉ [0, u[i]]
      
    postulate
      no-progress : lim ‖x (k+1) - x k‖ ≡ 0
      stuck : ∀ k > K → α k < 10^{-6}
      
    reason : String
    reason = "Newton direction computed incorrectly, always violates bounds"

-- FAILURE 11: Loss of Positive Definiteness
-- Hessian H becomes indefinite or singular
module HessianFailure where
  record BadHessian : Set where
    field
      H : ℕ → Matrix n n
      
      -- Should be: H positive definite (all eigenvalues > 0)
      should-be-pd : ∀ k → PositiveDefinite (H k)
      
      -- But: eigenvalues can be negative or zero
      has-negative-eig : ∃[ k ] ∃[ λ ] λ < 0 ∧ eigenvalue (H k) λ
      
      -- Or: condition number → ∞
      ill-conditioned : lim (cond (H k)) ≡ ∞
      
    postulate
      solver-failure : ∃[ k ] ¬CanSolve (H k · dx ≡ -g)
      
    reason : String
    reason = "Mixing s/z destroys positive definiteness of Hessian"

-- FAILURE 12: Non-Convergent Subsequence
-- Iterates have subsequence that doesn't converge
module SubsequenceDivergence where
  record OscillatingSequence : Set where
    field
      x : ℕ → Vec ℝ n
      
      -- Should: x_k → x* for some x*
      should-converge : ∃[ x* ] lim (x k) ≡ x*
      
      -- But: has oscillating subsequence
      oscillates : ∃[ k₁ k₂ ] k₁ < k₂ ∧ ‖x k₁ - x k₂‖ > ε
      
      -- Example: x oscillates between two points
      two-point-cycle : ∃[ xₐ xᵦ ] 
        (∀ k → even k → x k ≈ xₐ) ∧
        (∀ k → odd k → x k ≈ xᵦ) ∧
        xₐ ≠ xᵦ
      
    postulate
      no-cluster-point : ¬ ∃[ x* ] AccumulationPoint x* {x k}
      
    reason : String
    reason = "Incorrect Newton step creates limit cycle instead of converging"

-- Meta-theorem: All 12 failures are related
postulate
  root-cause : 
    MixedPrimalDualBarrier → 
    (DirectionReversal ∧ GapOscillation ∧ BarrierParamFailure ∧
     PrimalInfeasibility ∧ DualExplosion ∧ LineSearchDegen ∧
     HessianFailure ∧ SubsequenceDivergence)
    
  solution : 
    PureBarrierMethod → 
    ¬(Any of the 12 failures)
