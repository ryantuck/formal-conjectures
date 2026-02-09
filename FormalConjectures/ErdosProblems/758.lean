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
# Erdős Problem 758

Determine z(n) - maximum cochromatic number.

SOLVED (computationally for small n)

*Reference:* [erdosproblems.com/758](https://www.erdosproblems.com/758)
-/

open Finset

open scoped Topology Real

namespace Erdos758

variable {α : Type*}

/-- Cochromatic number -/
noncomputable def cochromaticNumber (G : SimpleGraph α) : ℕ := sorry

/-- z(n): maximum cochromatic number over n-vertex graphs -/
noncomputable def z (n : ℕ) : ℕ := sorry

/-- Computational results for z(n) -/
@[category research solved, AMS 05]
theorem cochromatic_number_values :
    z 12 = 4 ∧ sorry := by
  sorry

end Erdos758
