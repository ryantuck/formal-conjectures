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
# Erdős Problem 657

If A ⊂ ℝ² has n points with no isosceles triangles, must A determine at least
f(n)n distinct distances for some f(n) → ∞?

OPEN (problem of Erdős and Davies)

*Reference:* [erdosproblems.com/657](https://www.erdosproblems.com/657)
-/

open EuclideanSpace Metric Finset

open scoped Topology Real

namespace Erdos657

/-- No isosceles triangles: every 3 points determine 3 distinct distances -/
def NoIsoscelesTriangles (A : Finset (Fin 2 → ℝ)) : Prop := sorry

/-- No isosceles triangles implies f(n)n distinct distances with f(n) → ∞ -/
@[category research open, AMS 52]
theorem no_isosceles_many_distances (answer : Prop) :
    answer ↔ ∃ f : ℕ → ℝ, Filter.Tendsto f Filter.atTop Filter.atTop ∧
      ∀ᶠ (n : ℕ) in Filter.atTop, ∀ (A : Finset (Fin 2 → ℝ)),
        A.card = n → NoIsoscelesTriangles A →
        sorry ≥ Nat.floor (f n * n) := by
  sorry

end Erdos657
