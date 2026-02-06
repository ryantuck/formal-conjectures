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
# Erdős Problem 762

K₅-free chromatic vs cochromatic bound.

DISPROVED

*Reference:* [erdosproblems.com/762](https://www.erdosproblems.com/762)
-/

open Finset

open scoped Topology Real

namespace Erdos762

variable {α : Type*}

/-- Chromatic number -/
noncomputable def chromaticNumber (G : SimpleGraph α) : ℕ := sorry

/-- Cochromatic number -/
noncomputable def cochromaticNumber (G : SimpleGraph α) : ℕ := sorry

/-- Disproved: K₅-free with ζ ≥ 4 has χ ≤ ζ + 2 -/
@[category research solved, AMS 05]
theorem not_k5_free_chromatic_bound :
    ¬ ∀ (G : SimpleGraph α),
      G.CliqueFree 5 →
      cochromaticNumber G ≥ 4 →
      chromaticNumber G ≤ cochromaticNumber G + 2 := by
  sorry

end Erdos762
