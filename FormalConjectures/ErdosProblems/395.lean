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
# Erdős Problem 395

Given complex numbers $z_1,\ldots,z_n \in \mathbb{C}$ with $|z_i| = 1$, is the probability
that $|\epsilon_1 z_1 + \cdots + \epsilon_n z_n| \leq \sqrt{2}$ (with $\epsilon_i \in \{-1,1\}$ random)
at least $\gg 1/n$?

PROVED by He, Juškevičius, Narayanan, Spiro. The bound 1/n is optimal.

*Reference:* [erdosproblems.com/395](https://www.erdosproblems.com/395)
-/

open Filter Topology BigOperators Real Complex

namespace Erdos395

/-- He-Juškevičius-Narayanan-Spiro: Reverse Littlewood-Offord theorem -/
@[category research solved, AMS 11]
theorem erdos_395 :
    ∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, n > 0 → ∀ z : Fin n → ℂ,
      (∀ i, ‖z i‖ = 1) →
      ∃ S : Finset (Fin n → Bool), S.card ≥ ⌊c * 2^n / n⌋₊ ∧
        ∀ ε ∈ S, ‖∑ i, (if ε i then (1:ℂ) else -1) * z i‖ ≤ Real.sqrt 2 := by
  sorry

end Erdos395
