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
# Erdős Problem 439

In any finite colouring of the integers, must there exist two distinct integers x ≠ y
of the same colour such that x+y is a square? What about a k-th power?

Khalfalah-Szemerédi (2006): PROVED - For any non-constant polynomial f(z) ∈ ℤ[z]
where 2 | f(z) for some z ∈ ℤ, any finite colouring contains monochromatic pairs
x ≠ y with x+y = f(z).

*Reference:* [erdosproblems.com/439](https://www.erdosproblems.com/439)
-/

open Filter Topology BigOperators

namespace Erdos439

/-- Khalfalah-Szemerédi: Monochromatic pairs with square sum -/
@[category research solved, AMS 11]
theorem erdos_439_khalfalah_szemeredi_square :
    ∀ n : ℕ, n > 0 → ∀ c : ℕ → Fin n, ∃ x y : ℕ, x ≠ y ∧ c x = c y ∧ ∃ k : ℕ, x + y = k ^ 2 := by
  sorry

/-- Khalfalah-Szemerédi: General polynomial case -/
@[category research solved, AMS 11]
theorem erdos_439_khalfalah_szemeredi_general :
    ∀ f : Polynomial ℤ, f ≠ 0 → (∃ z : ℤ, 2 ∣ f.eval z) →
      ∀ n : ℕ, n > 0 → ∀ c : ℕ → Fin n, ∃ x y : ℕ, x ≠ y ∧ c x = c y ∧ ∃ z : ℤ, (x : ℤ) + y = f.eval z := by
  sorry

end Erdos439
