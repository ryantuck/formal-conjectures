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
# Erdős Problem 664

Let c<1 and A₁,...,Aₘ ⊆ {1,...,n} with |Aᵢ|>c√n and pairwise intersections ≤ 1.
Must there exist B intersecting all Aᵢ with |B∩Aᵢ| ≪_c 1?

DISPROVED by Alon using projective plane

*Reference:* [erdosproblems.com/664](https://www.erdosproblems.com/664)
-/

open Finset

open scoped Topology Real

namespace Erdos664

/-- Negation: counterexample exists -/
@[category research solved, AMS 05]
theorem not_small_intersecting_set (c : ℝ) (hc : c < 1) :
    ¬ ∀ᶠ (n : ℕ) in Filter.atTop,
      ∀ (family : Finset (Finset ℕ)),
        (∀ A ∈ family, A.card > Nat.floor (c * Real.sqrt n)) →
        (∀ A B, A ∈ family → B ∈ family → A ≠ B → (A ∩ B).card ≤ 1) →
        ∃ (B : Finset ℕ), (∀ A ∈ family, (B ∩ A).Nonempty) ∧
          ∃ M : ℕ, ∀ A ∈ family, (B ∩ A).card ≤ M := by
  sorry

end Erdos664
