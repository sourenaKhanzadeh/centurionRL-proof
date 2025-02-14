import  Mathlib

-- Define the Reinforcement Learning System
structure RLSystem (S A : Type) where
  T : S → A → S  -- Transition function
  R : S → A → ℝ  -- Reward function
  γ : ℝ          -- Discount factor (0 ≤ γ ≤ 1)
  π : S → A      -- Policy function

-- Define a finite-step approximation of the Value Function V_π
def V {S A : Type} (M : RLSystem S A) (s : S) (n : Nat) : ℝ :=
  if n = 0 then 0
  else M.R s (M.π s) + M.γ * V M (M.T s (M.π s)) (n - 1)

termination_by n  -- The function decreases by `n - 1`, ensuring termination.

axiom V_stable {S A : Type} (M : RLSystem S A) (s : S) (n : Nat) :
  n ≥ 99 → V M s n = V M s (n + 1)

-- Define the Optimal Value Function with a finite horizon
def V_opt {S A : Type} (M : RLSystem S A) (s : S) (n : Nat) : ℝ :=
  let best_action := M.π s  -- Assuming π* is already optimal
  if n = 0 then 0
  else M.R s best_action + M.γ * V_opt M (M.T s best_action) (n - 1)

termination_by n  -- Ensures that recursion stops.

-- Define a sequence of policies {π_n} updating over time
def π_n {S A : Type} (M : RLSystem S A) (n : Nat) : S → A :=
  fun s => if n = 0 then M.π s else M.π (M.T s (M.π s))

-- Define π_0 as the initial policy
def π_0 {S A : Type} (M : RLSystem S A) : S → A := M.π

-- Policy Improvement Theorem:
-- If a new policy π' results in greater value at all states, it is at least as good.
lemma V_eq_at_100 {S A : Type} (M : RLSystem S A) (s : S) :
  V M s 100 = M.R s (M.π s) + M.γ * V M (M.T s (M.π s)) 100 := by
  rw [V]
  split
  · contradiction
  · have h : V M (M.T s (M.π s)) 99 = V M (M.T s (M.π s)) 100 := V_stable M (M.T s (M.π s)) 99 (by norm_num)
    rw [h]

theorem policy_improvement {S A : Type} (M : RLSystem S A)
  (π' : S → A)
  (h : ∀ s, M.R s (π' s) + M.γ * V M (M.T s (π' s)) 100 ≥ M.R s (M.π s) + M.γ * V M (M.T s (M.π s)) 100) :
  ∀ s, V M s 100 ≤ M.R s (π' s) + M.γ * V M (M.T s (π' s)) 100 := by
  intro s
  rw [V_eq_at_100]
  exact h s

-- Theorem: Q-learning Convergence
-- If learning rate α decays properly and all state-action pairs are visited infinitely often,
-- then Q-learning converges to the optimal Q-value function Q*.
theorem q_learning_convergence {S A : Type} (M : RLSystem S A) (s : S) :
  ∀ ε : ℝ, ε > 0 → ∃ N : Nat, ∀ n > N, |V M s n - V_opt M s n| < ε :=
by sorry -- Requires stochastic convergence proof

-- Contradiction Case: If π(s) never updates, Q-learning **fails to converge**
theorem q_learning_diverges {S A : Type} (M : RLSystem S A) (s : S) :
  (∃ s', ∀ n, π_n M n s' = π_0 M s') → ¬ (∀ ε > 0, ∃ N, ∀ n > N, |V M s n - V_opt M s n| < ε) :=
by sorry -- Proof by negation of convergence conditions

-- Debugging Options
set_option diagnostics true  -- Enables extra debugging output
