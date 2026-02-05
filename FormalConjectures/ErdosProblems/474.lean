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
# Erdős Problem 474

Under what set theoretic assumptions is it true that ℝ² can be 3-colored such that
for every uncountable A ⊆ ℝ², A² contains a pair of each color?

Equivalently: When is 2^(ℵ₀) ↛ [ℵ₁]³²?

Erdős (1954): TRUE under CH (𝔠 = ℵ₁).
Shelah: Proved consistency of the opposite (2^(ℵ₀) → [ℵ₁]³²) with large 𝔠.

Prize: $100 (Erdős).

*Reference:* [erdosproblems.com/474](https://www.erdosproblems.com/474)
-/

open Filter Topology BigOperators Real Classical

namespace Erdos474

/-- Erdős: Three-coloring under CH -/
@[category research solved, AMS 11]
theorem erdos_474_under_ch :
    (Cardinal.mk ℝ = Cardinal.aleph 1) →
      ∃ c : ℝ × ℝ → Fin 3, ∀ A : Set ℝ, ¬A.Countable →
        ∀ i : Fin 3, ∃ x y : ℝ, x ∈ A ∧ y ∈ A ∧ c (x, y) = i := by
  sorry

end Erdos474
