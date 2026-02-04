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
# Erdős Problem 186

*Reference:* [erdosproblems.com/186](https://www.erdosproblems.com/186)

Let $F(N)$ be the maximal size of $A\subseteq \{1,\ldots,N\}$ which is 'non-averaging', so that
no $n\in A$ is the arithmetic mean of at least two elements in $A$. What is the order of
growth of $F(N)$?
-/

namespace Erdos186

open Finset Real Classical

/--
A set A is non-averaging if no element n in A is the arithmetic mean of a subset S of A
with at least two elements.
-/
def IsNonAveraging (A : Finset ℕ) : Prop :=
  ∀ (n : ℕ) (_ : n ∈ A), ∀ (S : Finset ℕ), S ⊆ A → S.card ≥ 2 →
    (∑ x ∈ S, (x : ℝ)) / S.card ≠ (n : ℝ)

/--
F(N) is the maximal size of a non-averaging subset of {1, ..., N}.
-/
noncomputable def F (N : ℕ) : ℕ :=
  sSup { k | ∃ (A : Finset ℕ), k = A.card ∧ A ⊆ Icc 1 N ∧ IsNonAveraging A }

/--
Erdős asked for the order of growth of F(N).
It is known that F(N) = N^(1/4 + o(1)).
The lower bound N^(1/4) is due to Bosznay [Bo89] and the upper bound
N^(1/4 + o(1)) to Pham and Zakharov [PhZa24].
-/
@[category research solved, AMS 05 11]
theorem erdos_186 :
    ∀ ε > 0, ∀ᶠ (N : ℕ) in Filter.atTop, (N : ℝ) ^ (1 / 4 - ε) ≤ (F N : ℝ) ∧ (F N : ℝ) ≤ (N : ℝ) ^ (1 / 4 + ε) := by
  sorry

end Erdos186
