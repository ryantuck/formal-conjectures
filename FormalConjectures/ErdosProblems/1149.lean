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
# Erdős Problem 1149

Density of coprime pairs involving floor functions.

PROVED

*Reference:* [erdosproblems.com/1149](https://www.erdosproblems.com/1149)
-/

open Finset Filter Nat

open scoped Topology Real

namespace Erdos1149

/-- For any non-integer positive real α, the natural density of integers n ≥ 1
    such that gcd(n, ⌊n^α⌋) = 1 equals 6/π². Proved by Bergelson and Richter. -/
@[category research solved, AMS 11]
theorem coprime_floor_density :
    ∀ (α : ℝ), α > 0 → (∀ (m : ℤ), α ≠ m) →
    ∃ (d : ℝ), d = 6 / Real.pi^2 ∧
    Tendsto (fun N : ℕ => (Finset.filter (fun n =>
      n ≥ 1 ∧ Nat.gcd n ⌊(n : ℝ)^α⌋₊ = 1) (Finset.range (N + 1))).card / (N : ℝ))
      atTop (𝓝 d) := by
  sorry

end Erdos1149
