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
# Erdős Problem 782

Quasi-progressions and cubes in squares.

OPEN

*Reference:* [erdosproblems.com/782](https://www.erdosproblems.com/782)
-/

open Finset

open scoped Topology Real

namespace Erdos782

/-- Squares contain arbitrarily long quasi-progressions -/
@[category research open, AMS 11]
theorem squares_quasi_progressions (answer : Prop) :
    answer ↔ ∀ k : ℕ, ∃ (S : Finset ℕ),
      S.card = k ∧
      (∀ s ∈ S, ∃ n : ℕ, s = n ^ 2) ∧
      sorry := by
  sorry

/-- Squares contain arbitrarily large cubes -/
@[category research open, AMS 11]
theorem squares_contain_cubes (answer : Prop) :
    answer ↔ ∀ k : ℕ, ∃ (C : Finset ℕ),
      C.card = k ∧
      sorry := by
  sorry

end Erdos782
