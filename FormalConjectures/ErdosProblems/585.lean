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
# Erdős Problem 585

What is the maximum number of edges a graph on n vertices can have if it contains
no two edge-disjoint cycles on the same vertex set?

OPEN (bounds: n log log n to n (log n)^O(1))

*Reference:* [erdosproblems.com/585](https://www.erdosproblems.com/585)
-/

open SimpleGraph

open scoped Topology Real

namespace Erdos585

variable {α : Type*}

/-- Max edges with no two edge-disjoint cycles on same vertex set -/
noncomputable def maxEdges (n : ℕ) : ℕ := sorry

/-- Lower bound: ≥ n log log n -/
@[category research open, AMS 05]
theorem lower_bound :
    ∃ c : ℝ, c > 0 ∧ ∀ᶠ (n : ℕ) in Filter.atTop,
      (maxEdges n : ℝ) ≥ c * (n : ℝ) * Real.log (Real.log n) := by
  sorry

/-- Upper bound: ≤ n (log n)^O(1) -/
@[category research open, AMS 05]
theorem upper_bound :
    ∃ c k : ℝ, c > 0 ∧ k > 0 ∧ ∀ᶠ (n : ℕ) in Filter.atTop,
      (maxEdges n : ℝ) ≤ c * (n : ℝ) * (Real.log n) ^ k := by
  sorry

end Erdos585
