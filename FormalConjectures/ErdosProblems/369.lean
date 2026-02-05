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
# Erdős Problem 369

Let $\epsilon > 0$ and $k \geq 2$. For all sufficiently large $n$, does there exist a
sequence of $k$ consecutive integers in $\{1,\ldots,n\}$ all of which are $n^\epsilon$-smooth?

Note: The literal problem is trivially true. Two non-trivial variants:
1. Each m must be m^ε-smooth (Balog-Wooley: YES)
2. Each m must lie in [n/2, n] (OPEN for all large n)

*Reference:* [erdosproblems.com/369](https://www.erdosproblems.com/369)
-/

open Filter Topology BigOperators Real

namespace Erdos369

/-- A number is B-smooth if all its prime factors are at most B -/
def IsSmooth (n B : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → p ≤ B

/-- Balog-Wooley: Each number m is m^ε-smooth -/
@[category research solved, AMS 11]
theorem erdos_369_balog_wooley :
    ∀ ε > 0, ∀ k : ℕ, k ≥ 2 → ∀ᶠ n : ℕ in atTop,
      ∃ m : ℕ, m ≤ n ∧ ∀ i < k,
        IsSmooth (m + i) ⌊(m + i : ℝ) ^ ε⌋₊ := by
  sorry

/-- Open variant: k consecutive smooth numbers in [n/2, n] -/
def erdos_369_conjecture : Prop :=
  ∀ ε > 0, ∀ k : ℕ, k ≥ 2 → ∀ᶠ n : ℕ in atTop,
    ∃ m : ℕ, n/2 ≤ m ∧ m ≤ n ∧ ∀ i < k,
      IsSmooth (m + i) ⌊(n : ℝ) ^ ε⌋₊

end Erdos369
