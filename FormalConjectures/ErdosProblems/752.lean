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
# Erdős Problem 752

Graph with min degree k and girth >2s has many cycle lengths.

PROVED

*Reference:* [erdosproblems.com/752](https://www.erdosproblems.com/752)
-/

open Finset

open scoped Topology Real

namespace Erdos752

variable {α : Type*}

/-- Number of distinct cycle lengths in a graph -/
noncomputable def numDistinctCycleLengths (G : SimpleGraph α) : ℕ := sorry

/-- Graphs with min degree k and large girth have many cycle lengths -/
@[category research solved, AMS 05]
theorem min_degree_girth_cycle_lengths (k s : ℕ) :
    ∃ C : ℝ, C > 0 ∧
      ∀ (G : SimpleGraph α) [DecidableRel G.Adj] [G.LocallyFinite],
        (∀ v : α, G.degree v ≥ k) →
        G.girth > 2 * s →
        numDistinctCycleLengths G ≥ C * (k : ℝ) ^ s := by
  sorry

end Erdos752
