/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 856

fₖ(N) for identical pairwise LCMs.

OPEN

*Reference:* [erdosproblems.com/856](https://www.erdosproblems.com/856)
-/

open Finset Nat

open scoped Topology Real BigOperators

namespace Erdos856

/-- A k-subset has identical pairwise LCMs -/
def IdenticalPairwiseLCMs (S : Finset ℕ) (k : ℕ) : Prop :=
  ∃ (T : Finset ℕ), T ⊆ S ∧ T.card = k ∧
    ∃ ℓ : ℕ, ∀ a b, a ∈ T → b ∈ T → a ≠ b → Nat.lcm a b = ℓ

/-- fₖ(N): max reciprocal sum over subsets with no k-subset having identical pairwise LCMs -/
noncomputable def f_k (k N : ℕ) : ℝ :=
  sSup {x : ℝ | ∃ A : Finset ℕ, (∀ n ∈ A, n ≤ N) ∧ ¬IdenticalPairwiseLCMs A k ∧
    x = ∑ n ∈ A, (1 : ℝ) / n}

/-- Erdős upper bound: fₖ(N) ≪ log N / log log N -/
@[category research open, AMS 11]
theorem erdos_upper_bound (k : ℕ) (hk : k ≥ 3) :
    ∃ C : ℝ, ∀ N : ℕ, N ≥ 2 →
      f_k k N ≤ C * (Real.log N) / (Real.log (Real.log N)) := by
  sorry

/-- Tang-Zhang bounds: (log N)^(b_k - o(1)) ≤ fₖ(N) ≤ (log N)^(c_k + o(1)) -/
@[category research open, AMS 11]
theorem tang_zhang_bounds (k : ℕ) (hk : k ≥ 3) :
    ∃ b_k c_k : ℝ, 0 < b_k ∧ b_k < c_k ∧
      (∀ ε > 0, ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
        (Real.log N) ^ (b_k - ε) ≤ f_k k N ∧
        f_k k N ≤ (Real.log N) ^ (c_k + ε)) := by
  sorry

end Erdos856
