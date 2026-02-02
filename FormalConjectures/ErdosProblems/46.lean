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
# Erdős Problem 46

*Reference:* [erdosproblems.com/46](https://www.erdosproblems.com/46)
-/

namespace Erdos46

open scoped BigOperators

/--
Does every finite colouring of the integers have a monochromatic solution to $1=\sum \frac{1}{n_i}$
with $2\leq n_1<\cdots <n_k$?

Croot [Cr03] proved that the answer is yes.

[Cr03] E. Croot, _On a coloring conjecture about unit fractions_, Annals of Mathematics (2003), 545–556.
-/
@[category research solved, AMS 11]
theorem erdos_46 : answer(True) ↔ ∀ (k : ℕ) (c : ℕ → Fin k), ∃ (S : Finset ℕ),
    (∀ n ∈ S, 2 ≤ n) ∧
    (∃ i, ∀ n ∈ S, c n = i) ∧
    ∑ n ∈ S, (1 : ℚ) / n = 1 := by
  sorry

end Erdos46
