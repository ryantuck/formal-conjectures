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
# Erdős Problem 336

For $r \geq 2$, let $h(r)$ be the maximum finite $k$ such that there exists a basis $A$
of order $r$ with exact order $k$. Find $\lim_{r \to \infty} h(r)/r^2$.

Known bounds: $1/3 \leq \lim h(r)/r^2 \leq 1/2$ (Grekos 1988, Nash 1993).
Computed values: $h(2) = 4$, $h(3) = 7$, $10 \leq h(4) \leq 11$.

*Reference:* [erdosproblems.com/336](https://www.erdosproblems.com/336)
-/

open Filter Topology BigOperators Real

namespace Erdos336

/-- A is a basis of order r if every large n is a sum of at most r elements from A -/
def IsBasisOfOrder (A : Set ℕ) (r : ℕ) : Prop :=
  ∃ N₀ : ℕ, ∀ n ≥ N₀, ∃ S : Finset ℕ, (∀ a ∈ S, a ∈ A) ∧ S.card ≤ r ∧ S.sum id = n

/-- A has exact order k if every large n is a sum of exactly k elements from A -/
def HasExactOrder (A : Set ℕ) (k : ℕ) : Prop :=
  ∃ N₀ : ℕ, ∀ n ≥ N₀, ∃ S : Finset ℕ, (∀ a ∈ S, a ∈ A) ∧ S.card = k ∧ S.sum id = n

/-- The maximum finite exact order for bases of order r -/
noncomputable def h (r : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ A : Set ℕ, IsBasisOfOrder A r ∧ HasExactOrder A k}

/-- Grekos (1988): Lower bound of 1/3 -/
@[category research open, AMS 11]
theorem erdos_336_grekos_lower :
    Filter.liminf (fun r => (h r : ℝ) / r^2) atTop ≥ 1/3 := by
  sorry

/-- Nash (1993): Upper bound of 1/2 -/
@[category research open, AMS 11]
theorem erdos_336_nash_upper :
    Filter.limsup (fun r => (h r : ℝ) / r^2) atTop ≤ 1/2 := by
  sorry

/-- Computed values -/
@[category research open, AMS 11]
theorem erdos_336_small_values : h 2 = 4 ∧ h 3 = 7 ∧ 10 ≤ h 4 ∧ h 4 ≤ 11 := by
  sorry

end Erdos336
