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
# Erdős Problem 718

Graphs with ≥ Cr^2n edges contain subdivision of K_r.

PROVED

*Reference:* [erdosproblems.com/718](https://www.erdosproblems.com/718)
-/

open Finset

open scoped Topology Real

namespace Erdos718

variable {α : Type*}

/-- Graph contains subdivision of K_r -/
def containsSubdivisionKr (G : SimpleGraph α) (r : ℕ) : Prop := sorry

/-- Edge threshold for subdivision -/
@[category research solved, AMS 05]
theorem edge_subdivision_threshold (r : ℕ) :
    ∃ C : ℝ, C > 0 ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        G.edgeFinset.card ≥ C * r ^ 2 * n →
        containsSubdivisionKr G r := by
  sorry

end Erdos718
