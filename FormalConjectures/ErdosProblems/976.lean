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
# Erdős Problem 976

Greatest prime divisor of polynomial products.

OPEN

*Reference:* [erdosproblems.com/976](https://www.erdosproblems.com/976)
-/

open Finset Filter Polynomial

open scoped Topology Real

namespace Erdos976

/-- Greatest prime divisor of product of polynomial values -/
noncomputable def F (f : ℤ[X]) (n : ℕ) : ℕ := sorry

/-- Growth of greatest prime divisor -/
@[category research open, AMS 11]
theorem prime_divisor_product_growth (f : ℤ[X]) (answer : Prop) :
    answer ↔ f.degree ≥ 2 → Irreducible f →
      ∃ (c : ℝ), 0 < c ∧
        ∀ᶠ n in atTop, (n : ℝ) ^ (1 + c) ≤ F f n := by
  sorry

end Erdos976
