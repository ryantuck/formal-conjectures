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
# Erdős Problem 724

Is f(n) ≫ n^(1/2) for mutually orthogonal Latin squares?

OPEN

*Reference:* [erdosproblems.com/724](https://www.erdosproblems.com/724)
-/

open Finset

open scoped Topology Real

namespace Erdos724

/-- Maximum number of mutually orthogonal Latin squares of order n -/
noncomputable def f (n : ℕ) : ℕ := sorry

/-- Conjecture: f(n) ≫ n^(1/2) -/
@[category research open, AMS 05]
theorem orthogonal_latin_squares_bound (answer : Prop) :
    answer ↔ ∃ c : ℝ, c > 0 ∧
      ∀ᶠ (n : ℕ) in Filter.atTop, f n ≥ c * (n : ℝ) ^ (1/2 : ℝ) := by
  sorry

end Erdos724
