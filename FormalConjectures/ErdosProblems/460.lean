/-
Copyright 2025 The Formal Conjectures Authors.

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
# Erdős Problem 460

Let a₀ = 0 and a₁ = 1. Define aₖ as the smallest integer greater than aₖ₋₁ such that
gcd(n-aₖ, n-aᵢ) = 1 for all 0 ≤ i < k.

Does the sum ∑_{0<aᵢ<n} 1/aᵢ diverge as n → ∞?

Eggleton-Erdős-Selfridge: aₖ < k^(2+o(1)).
Conjecture: aₖ ≪ k log k.

*Reference:* [erdosproblems.com/460](https://www.erdosproblems.com/460)
-/

open Filter Topology BigOperators Real Classical

namespace Erdos460

/-- The greedy coprime sequence relative to n -/
noncomputable def a (n : ℕ) : ℕ → ℕ := sorry

/-- Eggleton-Erdős-Selfridge: Growth bound -/
@[category research open, AMS 11]
theorem erdos_460_ees :
    ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ k : ℕ,
      (a n k : ℝ) < (k : ℝ) ^ (2 + ε) := by
  sorry

/-- Main question: Does the sum diverge? -/
@[category research open, AMS 11]
theorem erdos_460_divergence :
    Tendsto (fun n : ℕ => ((Finset.range n).filter (fun k => a n k < n ∧ k > 0)).sum
      (fun k => (1 : ℝ) / (a n k))) atTop atTop := by
  sorry

end Erdos460
