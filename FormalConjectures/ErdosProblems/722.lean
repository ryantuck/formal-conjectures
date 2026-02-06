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
# Erdős Problem 722

Existence of Steiner systems r-(n,k,1).

PROVED

*Reference:* [erdosproblems.com/722](https://www.erdosproblems.com/722)
-/

open Finset

open scoped Topology Real

namespace Erdos722

/-- Steiner system r-(n,k,1) exists for large n -/
@[category research solved, AMS 05]
theorem steiner_system_exists (r k : ℕ) (hk : k > r) :
    ∀ᶠ (n : ℕ) in Filter.atTop,
      ∃ (F : Finset (Finset (Fin n))),
        (∀ A ∈ F, A.card = k) ∧
        (∀ B : Finset (Fin n), B.card = r →
          ∃! A, A ∈ F ∧ B ⊆ A) := by
  sorry

end Erdos722
