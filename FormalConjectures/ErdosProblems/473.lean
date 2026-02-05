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
# Erdős Problem 473

Is there a permutation a₁, a₂, ... of the positive integers such that aₖ + aₖ₊₁
is always prime?

Odlyzko: PROVED - Such a permutation exists.

Greedy variant (Watts): a₁ = 1, aₙ₊₁ = min{x : aₙ + x is prime and x ∉ {a₁,...,aₙ}}.
van Doorn: Not all primes occur as sums in the greedy sequence (e.g., 197).

*Reference:* [erdosproblems.com/473](https://www.erdosproblems.com/473)
-/

open Filter Topology BigOperators Real Classical

namespace Erdos473

/-- Odlyzko: Prime-sum permutation exists -/
@[category research solved, AMS 11]
theorem erdos_473_odlyzko :
    ∃ perm : ℕ → ℕ, Function.Bijective perm ∧ (∀ i, (perm i).Prime) ∧
      ∀ k : ℕ, (perm k + perm (k + 1)).Prime := by
  sorry

end Erdos473
