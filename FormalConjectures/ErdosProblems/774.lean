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
# Erdős Problem 774

Proportionately dissociated sets decomposition.

OPEN

*Reference:* [erdosproblems.com/774](https://www.erdosproblems.com/774)
-/

open Finset

open scoped Topology Real

namespace Erdos774

/-- Dissociated set -/
def IsDissociated (A : Set ℕ) : Prop := sorry

/-- Proportionately dissociated -/
def IsProportionatelyDissociated (A : Set ℕ) : Prop := sorry

/-- Finite union decomposition -/
@[category research open, AMS 11]
theorem proportionately_dissociated_decomposition (answer : Prop) :
    answer ↔ ∀ (A : Set ℕ),
      IsProportionatelyDissociated A →
      ∃ (n : ℕ) (B : Fin n → Set ℕ),
        (∀ i, IsDissociated (B i)) ∧
        A = ⋃ i, B i := by
  sorry

end Erdos774
