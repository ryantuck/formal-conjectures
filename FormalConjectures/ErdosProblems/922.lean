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
# Erdős Problem 922

Independent sets and chromatic number.

PROVED

*Reference:* [erdosproblems.com/922](https://www.erdosproblems.com/922)
-/

open Finset

open scoped Topology Real

namespace Erdos922

variable {α : Type*}

/-- Graphs with large independent sets have bounded chromatic number -/
@[category research solved, AMS 05]
theorem independent_chromatic :
    ∀ (G : SimpleGraph α) [Fintype α],
      (∃ (S : Finset α), G.IsIndepSet S ∧ (Fintype.card α : ℝ) / 2 < S.card) →
      G.chromaticNumber ≤ 3 := by
  sorry

end Erdos922
