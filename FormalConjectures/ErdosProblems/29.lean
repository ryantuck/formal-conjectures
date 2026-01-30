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
# Erdős Problem 29

*Reference:* [erdosproblems.com/29](https://www.erdosproblems.com/29)
-/

namespace Erdos29

open scoped BigOperators

/--
The number of representations of `n` as a sum of two elements of `A`.
This corresponds to the convolution $(1_A * 1_A)(n)$.
-/
noncomputable def representationCount (A : Set ℕ) (n : ℕ) : ℕ :=
  Set.ncard {p : ℕ × ℕ | p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n}

/--
Is there an explicit construction of a set $A \subseteq \mathbb{N}$ such that $A+A=\mathbb{N}$
but $1_A * 1_A(n) = o(n^\epsilon)$ for every $\epsilon > 0$?

The answer is yes, as proved by Jain, Pham, Sawhney, and Zakharov [JPSZ24].

[JPSZ24] V. Jain, H. Pham, M. Sawhney, and D. Zakharov, _Explicit constructions of sets with small sumset_,
arXiv:2401.02345 (2024).
-/
@[category research solved, AMS 11]
theorem erdos_29 : answer(True) ↔ ∃ A : Set ℕ,
    (∀ n, ∃ a ∈ A, ∃ b ∈ A, a + b = n) ∧
    ∀ ε > 0, (fun n ↦ (representationCount A n : ℝ)) =o[Filter.atTop] (fun n ↦ (n : ℝ) ^ ε) := by
  sorry

end Erdos29
