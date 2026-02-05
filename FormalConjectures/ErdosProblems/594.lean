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
# Erdős Problem 594

Does every graph G with chromatic number ≥ ℵ₁ contain all sufficiently large odd cycles?

PROVED by Erdős, Hajnal, and Shelah (1974)

*Reference:* [erdosproblems.com/594](https://www.erdosproblems.com/594)
-/

open SimpleGraph Cardinal

open scoped Topology Real

namespace Erdos594

variable {α : Type*}

/-- Chromatic number of a graph -/
noncomputable def chromaticNumber (G : SimpleGraph α) : Cardinal := sorry

/-- The cycle graph on n vertices -/
def cycleGraph (n : ℕ) : SimpleGraph (Fin n) := sorry

/-- χ(G) ≥ ℵ₁ implies G contains all large odd cycles -/
@[category research solved, AMS 03 05]
theorem uncountable_chromatic_contains_large_odd_cycles (G : SimpleGraph α)
    (hχ : chromaticNumber G ≥ aleph 1) :
    ∀ᶠ (k : ℕ) in Filter.atTop,
      ∃ (f : Fin (2*k+1) ↪ α), ∀ i j, (cycleGraph (2*k+1)).Adj i j ↔ G.Adj (f i) (f j) := by
  sorry

end Erdos594
