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
# Erdős Problem 1090

Monochromatic lines in colored finite sets.

PROVED

*Reference:* [erdosproblems.com/1090](https://www.erdosproblems.com/1090)
-/

open Finset

open scoped Topology Real

namespace Erdos1090

/-- Monochromatic k-point lines in 2-colored planar sets -/
@[category research solved, AMS 05]
theorem monochromatic_lines (k : ℕ) (hk : 3 ≤ k) :
    ∃ (A : Finset (EuclideanSpace ℝ (Fin 2))),
      ∀ (f : EuclideanSpace ℝ (Fin 2) → Fin 2),
        ∃ (L : Set (EuclideanSpace ℝ (Fin 2))) (c : Fin 2),
          sorry := by
  sorry

end Erdos1090
