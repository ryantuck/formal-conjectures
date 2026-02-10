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
# Erdős Problem 923

Triangle-free subgraphs and chromatic number.

PROVED

*Reference:* [erdosproblems.com/923](https://www.erdosproblems.com/923)
-/

open Finset

open scoped Topology Real

namespace Erdos923

variable {α : Type*}

/-- Graphs with large triangle-free subgraphs have bounded chromatic number -/
@[category research solved, AMS 05]
theorem triangle_free_chromatic (c : ℝ) (hc : 0 < c) :
    ∃ (f : ℝ → ℕ), ∀ (G : SimpleGraph α) [Fintype α] [DecidableRel G.Adj],
      (∃ (H : SimpleGraph α) (_ : DecidableRel H.Adj), H ≤ G ∧ H.CliqueFree 3 ∧
        c * (Fintype.card α : ℝ) ≤ H.edgeFinset.card) →
      G.chromaticNumber ≤ f (1 / c) := by
  sorry

end Erdos923
