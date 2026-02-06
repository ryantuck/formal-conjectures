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
# Erdős Problem 733

*Reference:* [erdosproblems.com/733](https://www.erdosproblems.com/733)

## Statement (PROVED)

A sequence 1 < X₁ ≤ ⋯ ≤ Xₘ ≤ n is "line-compatible" if there exists a set of n points
in ℝ² such that m lines ℓ₁,...,ℓₘ each contain at least two points, with exactly Xᵢ points
on line ℓᵢ.

**Main Result:** There are at most exp(O(n^{1/2})) line-compatible sequences.

Erdős noted it is easy to show at least exp(cn^{1/2}) such sequences exist for some c > 0,
but expected the upper bound to be difficult. He further asked whether the limit
lim_{n→∞} log(f(n))/n^{1/2} exists.

**Resolution:** Proved by Szemerédi and Trotter (1983). Related to Problems #607 and #732.

## Source
[Sze97a]
-/

open scoped Topology Real

namespace Erdos733

/-- A sequence X = (X₁, ..., Xₘ) with 1 < X₁ ≤ ... ≤ Xₘ ≤ n is line-compatible
if there exists a configuration of n points in ℝ² and m lines where line i contains
exactly Xᵢ points. -/
def LineCompatible (X : List ℕ) (n : ℕ) : Prop := sorry

/-- Count the number of line-compatible sequences for a given n -/
def numLineCompatibleSequences (n : ℕ) : ℕ := sorry

/-- Main theorem: The number of line-compatible sequences is at most exp(O(n^{1/2})) -/
@[category research solved, AMS 05]
theorem line_compatible_bound :
    ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n > 0 →
      (numLineCompatibleSequences n : ℝ) ≤ Real.exp (C * Real.sqrt n) := by
  sorry

/-- Lower bound: At least exp(cn^{1/2}) line-compatible sequences exist -/
@[category research solved, AMS 05]
theorem line_compatible_lower_bound :
    ∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, n > 0 →
      (numLineCompatibleSequences n : ℝ) ≥ Real.exp (c * Real.sqrt n) := by
  sorry

end Erdos733
