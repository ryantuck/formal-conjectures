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
# Erdős Problem 287

*Reference:* [erdosproblems.com/287](https://www.erdosproblems.com/287)
-/

open Filter Topology

namespace Erdos287

/--
Let k ≥ 2. For any distinct integers $1 < n_1 < \cdots < n_k$ satisfying
$1 = 1/n_1 + \cdots + 1/n_k$, must we have $\max(n_{i+1} - n_i) \geq 3$?

The example $1 = 1/2 + 1/3 + 1/6$ shows that 3 would be optimal.

The lower bound of ≥ 2 is equivalent to stating "1 is not the sum of reciprocals
of consecutive integers" (proven by Erdős, 1932).
-/
@[category research open, AMS 11]
theorem erdos_287 (k : ℕ) (hk : k ≥ 2) (n : Fin k → ℕ)
    (h_pos : ∀ i, n i > 1)
    (h_strict : ∀ i j, i < j → n i < n j)
    (h_sum : (1 : ℝ) = ∑ i : Fin k, (1 : ℝ) / (n i : ℝ)) :
    ∃ i : Fin k, ∃ j : Fin k, i.val + 1 = j.val ∧ n j - n i ≥ 3 := by
  sorry

/--
Erdős (1932): 1 is not the sum of reciprocals of consecutive integers.
This implies the lower bound max(n_{i+1} - n_i) ≥ 2.
-/
@[category research solved, AMS 11]
theorem erdos_287_gap_two :
    ¬ ∃ (k : ℕ) (n : Fin k → ℕ),
      (∀ i j, i < j → n j = n i + (j.val - i.val)) ∧
      (∀ i, n i > 0) ∧
      (1 : ℝ) = ∑ i : Fin k, (1 : ℝ) / (n i : ℝ) := by
  sorry

end Erdos287
