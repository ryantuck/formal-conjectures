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
# Erdős Problem 1140

*Reference:* [erdosproblems.com/1140](https://www.erdosproblems.com/1140)

## Statement (DISPROVED)

**Question:** Do there exist infinitely many n such that n - 2x² is prime for all x with 2x² < n?

**Answer:** No. Research by Epure and Gica has established that there are at most 9 such values.

**Known solutions:** The values of n satisfying this condition are: 2, 5, 7, 13, 31, 61, 181, 199

These eight values are likely the complete set, with at most one possible exception:
- For n ≡ 1 (mod 4): only 5, 13, 61, 181 qualify
- For n ≡ 3 (mod 4): only 7, 31, 199 qualify, plus possibly one additional exception

## Source
[Va99, 1.5]
-/

namespace Erdos1140

/-- Property: n - 2x² is prime for all x with 2x² < n -/
def satisfiesCondition (n : ℕ) : Prop :=
  ∀ x : ℕ, 2 * x^2 < n → (n - 2 * x^2).Prime

/-- Main result: There are only finitely many n satisfying the condition.
    The question "Do there exist infinitely many such n?" has been answered: No.
    Equivalently, the set of such n is finite (disproved by Epure and Gica). -/
@[category research solved, AMS 11]
theorem erdos_1140 :
    answer(True) ↔ {n : ℕ | satisfiesCondition n}.Finite := by
  sorry

/-- The known solutions -/
@[category research solved, AMS 11]
theorem known_solutions :
    {2, 5, 7, 13, 31, 61, 181, 199} ⊆ {n : ℕ | satisfiesCondition n} := by
  sorry

end Erdos1140
