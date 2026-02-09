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
# Erdős Problem 746

Random graph Hamiltonian threshold.

PROVED

*Reference:* [erdosproblems.com/746](https://www.erdosproblems.com/746)
-/

open Finset Filter

open scoped Topology Real

namespace Erdos746

variable {α : Type*}

/-- Graph is Hamiltonian -/
def isHamiltonian (G : SimpleGraph α) : Prop := sorry

/-- Random graphs with (1/2+ε)n log n edges are Hamiltonian -/
@[category research solved, AMS 05]
theorem random_graph_hamiltonian (ε : ℝ) (hε : ε > 0) :
    ∀ᶠ (n : ℕ) in atTop,
      ∀ (G : SimpleGraph (Fin n)),
        G.edgeSet.ncard ≥ ⌊(1/2 + ε) * n * Real.log n⌋₊ →
        isHamiltonian G := by
  sorry

end Erdos746
