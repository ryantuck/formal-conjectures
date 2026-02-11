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
# Erdős Problem 1112

Lacunary sequences and sumset gaps.

OPEN

*Reference:* [erdosproblems.com/1112](https://www.erdosproblems.com/1112)
-/

open Finset Filter

open scoped Real

namespace Erdos1112

/-- k-fold sumset: sums of k elements from A -/
def kSumset (k : ℕ) (A : Set ℕ) : Set ℕ :=
  {n | ∃ (s : Finset ℕ), s ⊆ A ∧ s.card = k ∧ s.sum id = n}

/-- Does there exist r (depending on d₁, d₂, k) such that for all lacunary sequences B
    with ratio >= r, there exists a sequence A with bounded gaps whose k-fold sumset avoids B -/
@[category research open, AMS 11]
theorem lacunary_sumset_avoidance (d₁ d₂ : ℕ) (hd : 1 ≤ d₁ ∧ d₁ < d₂) (k : ℕ) (hk : 3 ≤ k) :
    answer(sorry) ↔
      ∃ (r : ℕ), ∀ (B : ℕ → ℕ),
        (∀ i, B (i + 1) ≥ r * B i) →
        ∃ (A : ℕ → ℕ), StrictMono A ∧
          (∀ i, d₁ ≤ A (i + 1) - A i ∧ A (i + 1) - A i ≤ d₂) ∧
          Disjoint (kSumset k (Set.range A)) (Set.range B) := by
  sorry

end Erdos1112
