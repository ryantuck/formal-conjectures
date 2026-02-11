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
# Erdős Problem 1103

Growth rate of sequences with squarefree sumsets.

OPEN

*Reference:* [erdosproblems.com/1103](https://www.erdosproblems.com/1103)
-/

open Finset Filter

open scoped Real

namespace Erdos1103

/-- Growth rate of sequences with squarefree sumsets.
    Asks about growth rate of sequences A(n) where A(n)+A(n) consists only of squarefree numbers. -/
@[category research open, AMS 11]
theorem squarefree_sumset_growth :
    ∃ (A : ℕ → Finset ℕ),
      (∀ n, ∀ a ∈ A n, ∀ b ∈ A n, Squarefree (a + b)) ∧
      (∀ᶠ n in atTop, (A n).card ≥ n) := by
  sorry

end Erdos1103
