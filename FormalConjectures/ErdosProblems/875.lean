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
# Erdős Problem 875

Infinite set with disjoint sumsets - growth rate.

OPEN

*Reference:* [erdosproblems.com/875](https://www.erdosproblems.com/875)
-/

open Finset

open scoped Topology Real

namespace Erdos875

/-- r-fold sumset -/
def sumsetR (A : Set ℕ) (r : ℕ) : Set ℕ := sorry

/-- Growth and gaps for infinite disjoint sumsets -/
@[category research open, AMS 11]
theorem infinite_disjoint_sumsets_growth :
    ∃ (a : ℕ → ℕ), StrictMono a ∧
      (∀ r s : ℕ, r ≠ s → Disjoint (sumsetR {a n | n : ℕ} r) (sumsetR {a n | n : ℕ} s)) ∧
      sorry := by
  sorry

end Erdos875
