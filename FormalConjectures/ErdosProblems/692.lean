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
# Erdős Problem 692

Is δ₁(n,m) (density of integers with exactly one divisor in (n,m)) unimodal?

DISPROVED by Cambie with counterexamples

*Reference:* [erdosproblems.com/692](https://www.erdosproblems.com/692)
-/

open Nat

open scoped Topology Real

namespace Erdos692

/-- δ₁(n,m): density of integers with exactly one divisor in (n,m) -/
noncomputable def δ₁ (n m : ℕ) : ℝ := sorry

/-- Negation: δ₁(n,m) is not always unimodal -/
@[category research solved, AMS 11]
theorem not_unimodal_density_one_divisor :
    ¬ ∀ n : ℕ, ∀ m₁ m₂ m₃ : ℕ, n < m₁ → m₁ < m₂ → m₂ < m₃ →
      δ₁ n m₂ ≥ min (δ₁ n m₁) (δ₁ n m₃) := by
  sorry

end Erdos692
