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
# Erdős Problem 53

*Reference:* [erdosproblems.com/53](https://www.erdosproblems.com/53)
-/

namespace Erdos53

open scoped BigOperators

/--
Let $A$ be a finite set of integers. Is it true that, for every $k$, if $|A|$ is sufficiently large
depending on $k$, then there are at least $|A|^k$ many integers which are either the sum or
product of distinct elements of $A$?

Chang [Ch03] proved this.

[Ch03] M.-C. Chang, _Erdős-Szemerédi problem on sum set and product set_,
Annals of Mathematics (2003), 939–957.
-/
@[category research solved, AMS 11]
theorem erdos_53 : answer(True) ↔ ∀ (k : ℕ), ∃ (N₀ : ℕ), ∀ (A : Finset ℤ), N₀ ≤ A.card →
    let subsetSums := { s | ∃ (B : Finset ℤ), B ⊆ A ∧ B.Nonempty ∧ s = ∑ x ∈ B, x }
    let subsetProducts := { p | ∃ (B : Finset ℤ), B ⊆ A ∧ B.Nonempty ∧ p = ∏ x ∈ B, x }
    ((subsetSums ∪ subsetProducts).ncard : ℝ) ≥ (A.card : ℝ) ^ k := by
  sorry

end Erdos53
