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
# Erdős Problem 363

Are there only finitely many collections of disjoint intervals $I_1,\ldots,I_n$ with
$|I_i| \geq 4$ such that $\prod_{i=1}^n \prod_{m \in I_i} m$ is a perfect square?

DISPROVED: Ulas (2005), Bauer-Bennett (2007), Bennett-Van Luijk (2012) showed
infinitely many solutions exist for various values of n and interval sizes.

*Reference:* [erdosproblems.com/363](https://www.erdosproblems.com/363)
-/

open Filter Topology BigOperators

namespace Erdos363

/-- Product of integers in a set of intervals is a perfect square -/
def IntervalProductIsSquare (intervals : List (Finset ℕ)) : Prop :=
  ∃ k : ℕ, (intervals.map (fun I => I.prod id)).prod = k^2

/-- Ulas, Bauer-Bennett, Bennett-Van Luijk: Infinitely many solutions -/
@[category research solved, AMS 11]
theorem erdos_363_disproved :
    ∀ n ≥ 3, ∀ size ≥ 4, ∃ᶠ _ : ℕ in atTop,
      ∃ intervals : List (Finset ℕ),
        intervals.length = n ∧
        (∀ I ∈ intervals, I.card = size) ∧
        (∀ I ∈ intervals, ∀ J ∈ intervals, I ≠ J → Disjoint I J) ∧
        IntervalProductIsSquare intervals := by
  sorry

end Erdos363
