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
# Erdős Problem 388

Are there only finitely many solutions to:
$$\prod_{1 \leq i \leq k_1}(m_1+i) = \prod_{1 \leq j \leq k_2}(m_2+j)$$
where $k_1, k_2 > 3$ and $m_1 + k_1 \leq m_2$?

Generalization: For fixed $a, b$ and $k_1 > 2$, are there finitely many solutions to
$a \prod (m_1+i) = b \prod (m_2+j)$?

*Reference:* [erdosproblems.com/388](https://www.erdosproblems.com/388)
-/

open Filter Topology BigOperators

namespace Erdos388

/-- Conjecture: Finitely many solutions to consecutive product equation -/
def erdos_388_conjecture : Prop :=
  ∃ B : ℕ, ∀ k₁ k₂ m₁ m₂ : ℕ,
    k₁ > 3 → k₂ > 3 → m₁ + k₁ ≤ m₂ →
    (Finset.Ico (m₁ + 1) (m₁ + k₁ + 1)).prod id =
      (Finset.Ico (m₂ + 1) (m₂ + k₂ + 1)).prod id →
    m₁ ≤ B

/-- Generalized conjecture with coefficients -/
def erdos_388_general (a b k₁ : ℕ) : Prop :=
  k₁ > 2 → ∃ B : ℕ, ∀ k₂ m₁ m₂ : ℕ,
    a * (Finset.Ico (m₁ + 1) (m₁ + k₁ + 1)).prod id =
      b * (Finset.Ico (m₂ + 1) (m₂ + k₂ + 1)).prod id →
    m₁ ≤ B

end Erdos388
