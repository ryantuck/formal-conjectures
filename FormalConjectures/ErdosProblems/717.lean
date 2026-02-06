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
# Erdős Problem 717

Chromatic number vs subdivision bound: χ(G) ≪ (n^(1/2)/log n)σ(G).

PROVED

*Reference:* [erdosproblems.com/717](https://www.erdosproblems.com/717)
-/

open Finset

open scoped Topology Real

namespace Erdos717

variable {α : Type*}

/-- Chromatic number -/
noncomputable def chromaticNumber (G : SimpleGraph α) : ℕ := sorry

/-- Maximum k such that G contains a subdivision of K_k -/
noncomputable def σ (G : SimpleGraph α) : ℕ := sorry

/-- Chromatic number bound via subdivision -/
@[category research solved, AMS 05]
theorem chromatic_subdivision_bound :
    ∃ C : ℝ, C > 0 ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
        chromaticNumber G ≤ C * ((n : ℝ) ^ (1/2 : ℝ) / Real.log n) * σ G := by
  sorry

end Erdos717
