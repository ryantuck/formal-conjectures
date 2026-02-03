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
# Erdős Problem 156

*Reference:* [erdosproblems.com/156](https://www.erdosproblems.com/156)
-/

open Set Filter

namespace Erdos156

/--
Does there exist a maximal Sidon set $A\subset \{1,\ldots,N\}$ of size $O(N^{1/3})$?

It is known that the greedy construction of a maximal Sidon set in $\{1,\ldots,N\}$ has
size $\gg N^{1/3}$. Ruzsa [Ru98b] constructed a maximal Sidon set of size $\ll (N\log N)^{1/3}$.

[ESS94] P. Erdős, A. Sárközy, and V. T. Sós, "On sumsets of Sidon sets. I", J. Number Theory 47 (1994), 329–347.
[Ru98b] I. Z. Ruzsa, "An infinite maximal Sidon set", J. Number Theory 68 (1998), 18–26.
-/
@[category research open, AMS 11]
theorem erdos_156 : answer(sorry) ↔ ∃ C : ℝ, ∀ N : ℕ, ∃ A : Set ℕ,
    IsMaximalSidonSetIn A N ∧ (A.ncard : ℝ) ≤ C * (N : ℝ) ^ (1 / 3 : ℝ) := by
  sorry

end Erdos156
