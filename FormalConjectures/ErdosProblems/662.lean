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
# Erdős Problem 662

For points x₁,...,xₙ ∈ ℝ² with pairwise distances ≥ 1, is the number of distances ≤ t
at most f(t) with equality only for triangular lattice?

OPEN (problem of Erdős, Lovász, and Vesztergombi)

*Reference:* [erdosproblems.com/662](https://www.erdosproblems.com/662)
-/

open EuclideanSpace Metric Finset

open scoped Topology Real

namespace Erdos662

/-- Number of distances ≤ t maximized by triangular lattice -/
@[category research open, AMS 52]
theorem unit_distance_bound_triangular_lattice :
    ∃ f : ℝ → ℕ, ∀ (n : ℕ) (t : ℝ),
      ∀ (A : Finset (Fin 2 → ℝ)),
        (∀ x y, x ∈ A → y ∈ A → x ≠ y → dist x y ≥ 1) →
        sorry ≤ f t := by
  sorry

end Erdos662
