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
# Erdős Problem 335

Let $d(A)$ denote the density of $A \subseteq \mathbb{N}$. Characterize all pairs $A, B$
with positive density satisfying $d(A+B) = d(A) + d(B)$.

One construction uses irrational rotation: $A = \{n > 0 : \{n\theta\} \in X_A\}$ for
measurable sets $X_A, X_B \subseteq \mathbb{R}/\mathbb{Z}$ with $\mu(X_A + X_B) = \mu(X_A) + \mu(X_B)$.

Question: Do all such pairs arise from this construction?

*Reference:* [erdosproblems.com/335](https://www.erdosproblems.com/335)
-/

open Filter Topology BigOperators MeasureTheory Real

namespace Erdos335

/-- Density of a set -/
noncomputable def density (A : Set ℕ) : ℝ :=
  Filter.limsup (fun N => (Nat.card {n ∈ A | n ≤ N} : ℝ) / N) atTop

/-- Sumset A+B -/
def sumset (A B : Set ℕ) : Set ℕ :=
  {n : ℕ | ∃ a ∈ A, ∃ b ∈ B, n = a + b}

/-- Problem asks to characterize pairs with d(A+B) = d(A) + d(B) -/
def erdos_335 : Prop :=
  ∀ A B : Set ℕ, density A > 0 → density B > 0 →
    density (sumset A B) = density A + density B →
    ∃ θ : ℝ, Irrational θ ∧
      ∃ X_A X_B : Set (ℝ ⧸ (AddSubgroup.zmultiples (1 : ℝ))),
        (∀ n : ℕ, n ∈ A ↔ (n * θ : ℝ ⧸ (AddSubgroup.zmultiples (1 : ℝ))) ∈ X_A) ∧
        (∀ n : ℕ, n ∈ B ↔ (n * θ : ℝ ⧸ (AddSubgroup.zmultiples (1 : ℝ))) ∈ X_B)

end Erdos335
