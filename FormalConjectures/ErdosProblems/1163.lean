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
# Erdős Problem 1163

Arithmetic structure of orders of subgroups of S_n.

OPEN

*Reference:* [erdosproblems.com/1163](https://www.erdosproblems.com/1163)
-/

open Finset Filter

open scoped Topology Real

namespace Erdos1163

/-- Describe by statistical means the arithmetic structure of the orders of subgroups of S_n.
    (Problem of Erdős and Turán)

    The problem statement is somewhat vague. A formal statement would need to clarify
    what "describe by statistical means" entails - likely involving asymptotic density,
    distribution properties, or characterization of the set of possible subgroup orders. -/
@[category research open, AMS 20]
theorem arithmetic_structure_subgroup_orders :
    ∃ (orders : ℕ → Finset ℕ), ∀ n : ℕ,
      ∀ d ∈ orders n, d ∣ n.factorial := by
  sorry

end Erdos1163
