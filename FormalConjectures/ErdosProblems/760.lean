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
# Erdős Problem 760

Chromatic implies large cochromatic subgraph.

PROVED

*Reference:* [erdosproblems.com/760](https://www.erdosproblems.com/760)
-/

open Finset

open scoped Topology Real

namespace Erdos760

variable {α : Type*}

/-- Chromatic number -/
noncomputable def chromaticNumber (G : SimpleGraph α) : ℕ := sorry

/-- Cochromatic number -/
noncomputable def cochromaticNumber (G : SimpleGraph α) : ℕ := sorry

/-- Large chromatic implies large cochromatic subgraph -/
@[category research solved, AMS 05]
theorem chromatic_implies_cochromatic (m : ℕ) :
    ∃ c : ℝ, c > 0 ∧
      ∀ (G : SimpleGraph α),
        chromaticNumber G = m →
        ∃ (S : Set α), ∃ (H : SimpleGraph S),
          cochromaticNumber H ≥ c * m / Real.log m := by
  sorry

end Erdos760
