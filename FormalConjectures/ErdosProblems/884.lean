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
# Erdős Problem 884

Divisor reciprocal difference sum bound.

OPEN

*Reference:* [erdosproblems.com/884](https://www.erdosproblems.com/884)
-/

open Finset Nat

open scoped Topology Real BigOperators

namespace Erdos884

/-- Sum of reciprocals of pairwise differences -/
@[category research open, AMS 11]
theorem divisor_reciprocal_differences (n : ℕ) :
    ∀ (d : List ℕ),
      (∀ i : Fin d.length, d.get i ∣ n) →
      (∀ i j : Fin d.length, i < j → d.get i < d.get j) →
      ∑ i : Fin (d.length - 1), (1 : ℝ) / (d.get ⟨i.val + 1, sorry⟩ - d.get i) ≤ sorry := by
  sorry

end Erdos884
