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
# Erdős Problem 1111

Chromatic number and anticomplete vertex sets.

OPEN

*Reference:* [erdosproblems.com/1111](https://www.erdosproblems.com/1111)
-/

open Finset

open scoped Topology Real

namespace Erdos1111

/-- Chromatic number and anticomplete vertex sets -/
@[category research open, AMS 05]
theorem chromatic_anticomplete {n : ℕ} (k : ℕ) :
    ∃ (f : ℕ → ℕ), ∀ (G : SimpleGraph (Fin n)),
      G.chromaticNumber ≥ k →
      ∃ (S : Finset (Fin n)), S.card ≥ f n ∧
        (∀ u ∈ S, ∀ v ∈ S, u ≠ v → ¬G.Adj u v) := by
  sorry

end Erdos1111
