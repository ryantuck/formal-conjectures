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
# Erdős Problem 753

List chromatic number sum conjecture.

DISPROVED

*Reference:* [erdosproblems.com/753](https://www.erdosproblems.com/753)
-/

open Finset

open scoped Topology Real

namespace Erdos753

variable {α : Type*}

/-- List chromatic number -/
noncomputable def listChromaticNumber (G : SimpleGraph α) : ℕ := sorry

/-- Disproved: χ_L(G) + χ_L(G^c) > n^(1/2+c) -/
@[category research solved, AMS 05]
theorem not_list_chromatic_sum_bound :
    ¬ ∃ c : ℝ, c > 0 ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
        listChromaticNumber G + listChromaticNumber (Gᶜ) > (n : ℝ) ^ (1/2 + c) := by
  sorry

end Erdos753
