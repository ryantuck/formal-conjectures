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
# Erdős Problem 572

For k ≥ 3, show that ex(n; C_{2k}) ≫ n^{1+1/k}, where ex(n; C_{2k}) is the maximum
number of edges in an n-vertex graph avoiding even cycles of length 2k.

OPEN

*Reference:* [erdosproblems.com/572](https://www.erdosproblems.com/572)
-/

open SimpleGraph

open scoped Topology Real

namespace Erdos572

variable {α : Type*}

/-- The Turán number ex(n; G): maximum edges in an n-vertex graph avoiding G -/
noncomputable def extremalNumber (n : ℕ) (G : SimpleGraph α) : ℕ := sorry

/-- The cycle graph on n vertices -/
def cycleGraph (n : ℕ) : SimpleGraph (Fin n) := sorry

/-- For k ≥ 3, ex(n; C_{2k}) ≫ n^{1+1/k} -/
@[category research open, AMS 05]
theorem extremal_even_cycle_lower_bound (k : ℕ) (hk : k ≥ 3) :
    ∃ c : ℝ, c > 0 ∧ ∀ᶠ (n : ℕ) in Filter.atTop,
      (extremalNumber n (cycleGraph (2 * k)) : ℝ) ≥ c * (n : ℝ) ^ (1 + 1 / (k : ℝ)) := by
  sorry

end Erdos572
