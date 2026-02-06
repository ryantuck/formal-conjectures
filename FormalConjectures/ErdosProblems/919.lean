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
# Erdős Problem 919

Graph chromatic number on ordinal products.

OPEN

*Reference:* [erdosproblems.com/919](https://www.erdosproblems.com/919)
-/

open Finset

open scoped Topology Real

namespace Erdos919

/-- Chromatic number on ordinal products -/
@[category research open, AMS 03]
theorem chromatic_ordinal_product (answer : Prop) :
    answer ↔ ∃ (G : SimpleGraph (ω × ω)),
      G.chromaticNumber = ℵ₀ ∧
      ∀ n : ℕ, (G.induce (Finset.range n ×ˢ Finset.range n : Set (ℕ × ℕ))).chromaticNumber < ℵ₀ := by
  sorry

end Erdos919
