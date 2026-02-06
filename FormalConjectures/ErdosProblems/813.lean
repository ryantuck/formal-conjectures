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
# Erdős Problem 813

Minimum clique in triangle-containing graphs.

OPEN (bounds n^(1/3) ≪ h(n) ≪ n^(1/2))

*Reference:* [erdosproblems.com/813](https://www.erdosproblems.com/813)
-/

open Finset

open scoped Topology Real

namespace Erdos813

/-- h(n): minimum clique where every 7 vertices have triangle -/
noncomputable def h (n : ℕ) : ℕ := sorry

/-- Bounds for h(n) -/
@[category research open, AMS 05]
theorem triangle_seven_clique_bound :
    ∃ c₁ c₂ : ℝ, c₁ > 0 ∧ c₂ > 0 ∧
      ∀ (n : ℕ), c₁ * (n : ℝ) ^ (1/3 : ℝ) ≤ h n ∧
        h n ≤ c₂ * (n : ℝ) ^ (1/2 : ℝ) := by
  sorry

end Erdos813
