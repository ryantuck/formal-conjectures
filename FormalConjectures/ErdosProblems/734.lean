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
# Erdős Problem 734

Pairwise balanced block design with bounded block size multiplicity.

OPEN

*Reference:* [erdosproblems.com/734](https://www.erdosproblems.com/734)
-/

open Finset

open scoped Topology Real

namespace Erdos734

/-- Pairwise balanced block design -/
def PairwiseBalanced (A : Finset (Finset ℕ)) (n : ℕ) : Prop :=
  ∀ i j : Fin n, i ≠ j →
    ∃! B, B ∈ A ∧ {i.val, j.val} ⊆ B

/-- Block size multiplicity bound -/
@[category research open, AMS 05]
theorem pairwise_balanced_block_size_bound (answer : Prop) :
    answer ↔ ∀ᶠ (n : ℕ) in Filter.atTop,
      ∃ (A : Finset (Finset ℕ)),
        PairwiseBalanced A n ∧
        ∀ t : ℕ, (A.filter (fun B => B.card = t)).card ≤ sorry := by
  sorry

end Erdos734
