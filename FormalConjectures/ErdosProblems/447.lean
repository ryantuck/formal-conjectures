/-
Copyright 2025 The Formal Conjectures Authors.

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
# Erdős Problem 447

How large can a union-free collection F of subsets of [n] be? A collection is union-free
if there are no distinct sets A, B, C ∈ F satisfying A ∪ B = C.

Conjectures:
1. Must |F| = o(2^n)?
2. Perhaps even |F| < (1+o(1))C(n, ⌊n/2⌋)?

Kleitman (1971): PROVED - Established |F| < (1+o(1))C(n, ⌊n/2⌋).

*Reference:* [erdosproblems.com/447](https://www.erdosproblems.com/447)
-/

open Filter Topology BigOperators Real

namespace Erdos447

/-- A collection is union-free if no set is the union of two others -/
def UnionFree {α : Type*} [DecidableEq α] (F : Finset (Finset α)) : Prop :=
  ∀ A ∈ F, ∀ B ∈ F, ∀ C ∈ F, A ≠ B → A ≠ C → B ≠ C → A ∪ B ≠ C

/-- Kleitman: Union-free collections have size at most (1+o(1))C(n,⌊n/2⌋) -/
@[category research solved, AMS 11]
theorem erdos_447_kleitman :
    ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ F : Finset (Finset (Fin n)),
      UnionFree F →
        (F.card : ℝ) ≤ (1 + ε) * Nat.choose n (n / 2) := by
  sorry

end Erdos447
