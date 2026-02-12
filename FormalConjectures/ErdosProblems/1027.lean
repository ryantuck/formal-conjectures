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
# Erdős Problem 1027

Chromatic number of set families.

PROVED

STATUS: SOLVED

*Reference:* [erdosproblems.com/1027](https://www.erdosproblems.com/1027)
-/

open Finset

open scoped Topology Real

namespace Erdos1027

/-- English version: Set families with bounded size have many transversals -/@[category research solved, AMS 05]
theorem set_family_transversals (n : ℕ) :
    ∃ (c : ℝ), 0 < c ∧
      ∀ (F : Finset (Finset (Fin n))),
        (∀ S ∈ F, S.card = n) →
        F.card ≤ c * 2 ^ n →
        sorry := by
  sorry

end Erdos1027
