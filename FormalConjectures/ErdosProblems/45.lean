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
# Erdős Problem 45

*Reference:* [erdosproblems.com/45](https://www.erdosproblems.com/45)
-/

namespace Erdos45

open scoped BigOperators

/--
Let $k \ge 2$. Is there an integer $n_k$ such that, if $D = \{d : 1 < d < n_k, d \mid n_k\}$,
then for any $k$-colouring of $D$ there is a monochromatic subset $D' \subseteq D$ such that
$\sum_{d \in D'} \frac{1}{d} = 1$?

The answer is yes, as proved by Croot [Cr03].

[Cr03] E. Croot, _On a coloring conjecture about unit fractions_, Annals of Mathematics (2003), 545–556.
-/
@[category research solved, AMS 11]
theorem erdos_45 : answer(True) ↔ ∀ k ≥ 2, ∃ n_k : ℕ,
    let D := {d | 1 < d ∧ d < n_k ∧ d ∣ n_k}
    ∀ (c : ℕ → Fin k), ∃ (D' : Finset ℕ),
      ↑D' ⊆ D ∧
      (∃ i, ∀ d ∈ D', c d = i) ∧
      ∑ d ∈ D', (1 : ℚ) / d = 1 := by
  sorry

end Erdos45
