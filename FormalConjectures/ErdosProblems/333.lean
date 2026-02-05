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
# Erdős Problem 333

Let $A \subseteq \mathbb{N}$ be a set of density zero. Does there exist a set $B$ such that:
- $A \subseteq B+B$ (where $B+B$ denotes the sumset)
- $|B \cap \{1,\ldots,N\}| = o(N^{1/2})$ for all large $N$?

Erdős and Newman (1977) proved this holds for perfect squares, which already implied
a negative answer to this general question.

*Reference:* [erdosproblems.com/333](https://www.erdosproblems.com/333)
-/

open Filter Topology BigOperators Real

namespace Erdos333

/-- Density of a set -/
noncomputable def density (A : Set ℕ) : ℝ :=
  Filter.limsup (fun N => (Nat.card {n ∈ A | n ≤ N} : ℝ) / N) atTop

/-- Sumset B+B -/
def sumset (B : Set ℕ) : Set ℕ :=
  {n : ℕ | ∃ b₁ ∈ B, ∃ b₂ ∈ B, n = b₁ + b₂}

/-- Erdős-Newman disproved the general question -/
@[category research solved, AMS 11]
theorem erdos_333_disproved :
    ¬∀ A : Set ℕ, density A = 0 →
      ∃ B : Set ℕ, A ⊆ sumset B ∧
        ∀ ε > 0, ∀ᶠ N : ℕ in atTop,
          (Nat.card {n ∈ B | n ≤ N} : ℝ) < ε * (N : ℝ) ^ ((1:ℝ)/2) := by
  sorry

end Erdos333
