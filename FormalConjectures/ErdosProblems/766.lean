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
# Erdős Problem 766

Estimate f(n;k,l) for forbidden subgraphs.

OPEN

*Reference:* [erdosproblems.com/766](https://www.erdosproblems.com/766)
-/

open Finset

open scoped Topology Real

namespace Erdos766

/-- f(n;k,l): min ex(n;G) over graphs with k vertices and l edges -/
noncomputable def f (n k l : ℕ) : ℕ := sorry

/-- Monotonicity and bounds for f(n;k,l) -/
@[category research open, AMS 05]
theorem f_monotonicity_bounds (n k l : ℕ) (hl : k < l) (hl' : l ≤ k ^ 2 / 4) (answer : Prop) :
    answer ↔ Monotone (fun l' => f n k l') ∧ sorry := by
  sorry

end Erdos766
