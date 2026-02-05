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
# Erdős Problem 429

If $A \subseteq \mathbb{N}$ is sufficiently sparse and doesn't cover all residue classes
modulo any prime p, does there exist integer n such that n+a is prime for all a ∈ A?

DISPROVED by Weisenberg: Constructed sparse sets omitting residue classes modulo every prime,
yet no n makes A+n all primes.

*Reference:* [erdosproblems.com/429](https://www.erdosproblems.com/429)
-/

open Filter Topology BigOperators

namespace Erdos429

/-- Weisenberg: The conjecture is false -/
@[category research solved, AMS 11]
theorem erdos_429_disproved :
    ∃ A : Set ℕ, (∀ p : ℕ, p.Prime → ∃ r : ZMod p, ∀ a ∈ A, (a : ZMod p) ≠ r) ∧
      (∀ n : ℕ, ∃ a ∈ A, ¬(n + a).Prime) := by
  sorry

end Erdos429
