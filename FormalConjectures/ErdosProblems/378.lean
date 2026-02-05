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
# Erdős Problem 378

For $r \geq 0$, does the density of integers $n$ for which $\binom{n}{k}$ is squarefree
for at least $r$ values of $1 \leq k < n$ exist? Is this density positive?

Erdős-Graham proved that for fixed k, density of n with squarefree $\binom{n}{k}$ is zero.
Granville-Ramaré resolved the problem, showing the density exists and is positive.

*Reference:* [erdosproblems.com/378](https://www.erdosproblems.com/378)
-/

open Filter Topology BigOperators Real

namespace Erdos378

/-- A number is squarefree if no prime square divides it -/
def IsSquarefree (n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → ¬(p^2 ∣ n)

/-- Granville-Ramaré: The density exists and is positive -/
@[category research solved, AMS 11]
theorem erdos_378_granville_ramare :
    ∀ r : ℕ, ∃ d : ℝ, d > 0 ∧
      Tendsto (fun N => (Nat.card {n : ℕ | n ≤ N ∧
        (Nat.card {k : ℕ | 0 < k ∧ k < n ∧
          IsSquarefree (Nat.choose n k)} ≥ r)} : ℝ) / N) atTop (𝓝 d) := by
  sorry

end Erdos378
