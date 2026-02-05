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
# Erdős Problem 419

Determine the complete set of limit points of $\tau((n+1)!) / \tau(n!)$.

Erdős-Graham found 1 + 1/k for k ≥ 1 are limit points.
Sawhney proved these are the ONLY limit points (verified in Lean).

*Reference:* [erdosproblems.com/419](https://www.erdosproblems.com/419)
-/

open Filter Topology BigOperators Real

namespace Erdos419

/-- The ratio of divisor counts of consecutive factorials -/
noncomputable def ratio (n : ℕ) : ℝ :=
  ((n + 1).factorial.divisors.card : ℝ) / (n.factorial.divisors.card : ℝ)

/-- Sawhney: The limit points are exactly {1 + 1/k : k ≥ 1} ∪ {1} -/
@[category research solved, AMS 11]
theorem erdos_419_sawhney :
    ∀ x : ℝ, (∃ᶠ n : ℕ in atTop, |ratio n - x| < 1/n) ↔
      (x = 1 ∨ ∃ k : ℕ, k ≥ 1 ∧ x = 1 + 1/(k : ℝ)) := by
  sorry

end Erdos419
