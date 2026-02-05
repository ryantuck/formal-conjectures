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
# Erdős Problem 605

Is there a function f(n) → ∞ such that n points on the surface of a sphere in R³
can have at least f(n)·n pairs at the same distance?

PROVED

*Reference:* [erdosproblems.com/605](https://www.erdosproblems.com/605)
-/

open EuclideanSpace Metric Finset

open scoped Topology Real

namespace Erdos605

/-- Points on sphere with ≫ f(n)·n same-distance pairs, f(n) → ∞ -/
@[category research solved, AMS 52]
theorem sphere_same_distance_pairs :
    ∃ (f : ℕ → ℝ), Filter.Tendsto f Filter.atTop Filter.atTop ∧
      ∀ᶠ (n : ℕ) in Filter.atTop,
        ∃ (S : Finset (Fin 3 → ℝ)) (r : ℝ),
          S.card = n ∧
          (∀ p ∈ S, ‖p‖ = r) ∧
          ((S ×ˢ S).filter (fun (p, q) => p ≠ q ∧ dist p q = 1)).card ≥ Nat.floor (f n * n) := by
  sorry

/-- For radius √2, u_{√2}(n) ≍ n^{4/3} -/
@[category research solved, AMS 52]
theorem sphere_sqrt_two_bound :
    ∃ c₁ c₂ : ℝ, c₁ > 0 ∧ c₂ > 0 ∧ ∀ᶠ (n : ℕ) in Filter.atTop,
      ∀ (S : Finset (Fin 3 → ℝ)),
        S.card = n →
        (∀ p ∈ S, ‖p‖ = Real.sqrt 2) →
        c₁ * (n : ℝ) ^ (4 / 3) ≤ ((S ×ˢ S).filter (fun (p, q) => p ≠ q ∧ dist p q = 1)).card ∧
        ((S ×ˢ S).filter (fun (p, q) => p ≠ q ∧ dist p q = 1)).card ≤ c₂ * (n : ℝ) ^ (4 / 3) := by
  sorry

end Erdos605
