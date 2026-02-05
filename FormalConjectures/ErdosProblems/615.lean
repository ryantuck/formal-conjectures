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
# Erdős Problem 615

Does there exist c > 0 such that any graph with n vertices and ≥ (1/8-c)n² edges
must contain either K₄ or an independent set of size Ω(n/log n)?

DISPROVED by Fox, Loh, and Zhao

*Reference:* [erdosproblems.com/615](https://www.erdosproblems.com/615)
-/

open SimpleGraph

open scoped Topology Real

namespace Erdos615

variable {α : Type*} [Fintype α]

/-- Ramsey-Turán number rt(n; 4, n/log n) < (1/8 - c)n² is false -/
@[category research solved, AMS 05]
theorem not_ramsey_turan_bound :
    ¬ ∃ c > 0, ∀ᶠ (n : ℕ) in Filter.atTop, ∀ (G : SimpleGraph (Fin n)),
      G.edgeSet.ncard ≥ Nat.floor ((1 / 8 - c) * n^2) →
      (∃ (f : Fin 4 ↪ Fin n), ∀ i j, i ≠ j → G.Adj (f i) (f j)) ∨
      (∃ (S : Finset (Fin n)), (∀ i j, i ∈ S → j ∈ S → ¬ G.Adj i j) ∧
        S.card ≥ Nat.floor ((n : ℝ) / Real.log n)) := by
  sorry

end Erdos615
