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
# Erdős Problem 641

Does χ(G) ≥ f(k) imply G contains k edge-disjoint cycles on the same vertices?

DISPROVED by Janzer et al.

*Reference:* [erdosproblems.com/641](https://www.erdosproblems.com/641)
-/

open SimpleGraph

open scoped Topology Real

namespace Erdos641

variable {α : Type*}

/-- Chromatic number -/
noncomputable def chromaticNumber (G : SimpleGraph α) : ℕ := sorry

/-- Negation: chromatic number doesn't guarantee edge-disjoint cycles on same vertices -/
@[category research solved, AMS 05]
theorem not_chromatic_implies_edge_disjoint_cycles :
    ¬ ∃ f : ℕ → ℕ, ∀ k : ℕ, ∀ (G : SimpleGraph α),
      chromaticNumber G ≥ f k →
      sorry := by
  sorry

end Erdos641
