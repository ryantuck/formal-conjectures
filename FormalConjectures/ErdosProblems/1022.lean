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
# Erdős Problem 1022

Property B of hypergraphs.

PROVED

STATUS: SOLVED

*Reference:* [erdosproblems.com/1022](https://www.erdosproblems.com/1022)
-/

open Finset

open scoped Topology Real

namespace Erdos1022

variable {α : Type*}

/-- English version: Hypergraphs of size ≥t have chromatic number 2 -/@[category research solved, AMS 05]
theorem property_b_hypergraphs (t : ℕ) :
    ∃ (m : ℕ), ∀ (H : Finset (Finset α)) [Fintype α],
      (∀ e ∈ H, e.card = t) →
      m ≤ H.card →
      ∃ (c : α → Fin 2), ∀ e ∈ H, ∃ v ∈ e, ∃ w ∈ e, c v ≠ c w := by
  sorry

end Erdos1022
