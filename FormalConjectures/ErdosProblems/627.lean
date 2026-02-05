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
# Erdős Problem 627

Does the limit of f(n) / (n/(log n)²) exist, where f(n) is the maximum of χ(G)/ω(G)
over all graphs G on n vertices?

OPEN

*Reference:* [erdosproblems.com/627](https://www.erdosproblems.com/627)
-/

open SimpleGraph

open scoped Topology Real

namespace Erdos627

variable {α : Type*}

/-- Chromatic number -/
noncomputable def chromaticNumber (G : SimpleGraph α) : ℕ := sorry

/-- Clique number -/
noncomputable def cliqueNumber (G : SimpleGraph α) : ℕ := sorry

/-- f(n): max χ/ω ratio over n-vertex graphs -/
noncomputable def f (n : ℕ) : ℝ := sorry

/-- Does lim f(n) / (n/(log n)²) exist? -/
@[category research open, AMS 05]
theorem chromatic_clique_ratio_limit (answer : Prop) :
    answer ↔ ∃ L : ℝ, Filter.Tendsto
      (fun n => f n / ((n : ℝ) / (Real.log n) ^ 2))
      Filter.atTop (nhds L) := by
  sorry

end Erdos627
