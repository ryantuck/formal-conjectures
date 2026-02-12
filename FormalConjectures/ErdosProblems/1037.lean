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
# Erdős Problem 1037

Degree diversity and trivial subgraphs.

DISPROVED

STATUS: SOLVED

*Reference:* [erdosproblems.com/1037](https://www.erdosproblems.com/1037)
-/

open Finset

open scoped Topology Real

namespace Erdos1037

variable {α : Type*}

/-- English version: Distinct degree constraint relates to trivial subgraph size -/@[category research open, AMS 05]
theorem degree_diversity : answer(True) ↔ ∃ (f : ℕ → ℝ), (∀ n, 0 < f n) ∧
      ∀ᶠ (n : ℕ) in Filter.atTop, ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        (∀ v w : Fin n, v ≠ w → G.degree v ≠ G.degree w) →
        (∀ S : Finset (Fin n), (S.card : ℝ) ≥ f n →
          ∃ v ∈ S, ∃ w ∈ S, v ≠ w ∧ (G.Adj v w ∨ ¬G.Adj v w)) := by
  sorry

end Erdos1037
