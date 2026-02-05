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
# Erdős Problem 320

Let $S(N)$ count the number of distinct sums of the form $\sum_{n \in A} \frac{1}{n}$
for $A \subseteq \{1,\ldots,N\}$. Estimate $S(N)$.

Bleicher-Erdős established bounds using iterated logarithms.
Bettin, Grenié, Molteni, Sanna (2025) improved the lower bound.

*Reference:* [erdosproblems.com/320](https://www.erdosproblems.com/320)
-/

open Filter Topology BigOperators Real

namespace Erdos320

/-- The set of all distinct unit fraction sums from subsets of {1,...,N} -/
noncomputable def S (N : ℕ) : Set ℝ :=
  {r : ℝ | ∃ A : Finset ℕ, (∀ n ∈ A, 0 < n ∧ n ≤ N) ∧ r = A.sum (fun n => (1 : ℝ) / n)}

/-- Bleicher-Erdős lower bound (simplified form) -/
@[category research open, AMS 11]
theorem erdos_320_lower_bound :
    ∃ C : ℝ, ∀ᶠ N in atTop,
      log (Nat.card (S N)) ≥ (N : ℝ) / log N * (log 2 * C) := by
  sorry

/-- Bettin-Grenié-Molteni-Sanna (2025) improved lower bound -/
@[category research open, AMS 11]
theorem erdos_320_bgms_2025 :
    ∃ C : ℝ, ∀ᶠ N in atTop,
      log (Nat.card (S N)) ≥ (N : ℝ) / log N * (2 * log 2 * C) := by
  sorry

end Erdos320
