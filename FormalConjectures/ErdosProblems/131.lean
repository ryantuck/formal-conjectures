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
# Erdős Problem 131

*Reference:* [erdosproblems.com/131](https://www.erdosproblems.com/131)
-/

namespace Erdos131

open Finset Filter Real Classical

/--
No element `a ∈ A` divides the sum of any non-empty subset of `A \ {a}`.
-/
def IsDivSumFree (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ S ⊆ A.erase a, S ≠ ∅ → ¬ (a ∣ S.sum id)

/--
`F(N)` is the size of the largest `A ⊆ {1, ..., N}` satisfying `IsDivSumFree A`.
-/
noncomputable def F (N : ℕ) : ℕ :=
  sup (filter (fun A => A ⊆ Icc 1 N ∧ IsDivSumFree A) (powerset (Icc 1 N))) card

/--
The conjecture is that $F(N) > N^{1/2 - o(1)}$.
This is false. Pham and Zakharov [PhZa24] proved $F(N) \le N^{1/4 + o(1)}$.
-/
@[category research solved, AMS 11]
theorem erdos_131 :
    answer(False) ↔ ∀ ε > 0, ∃ C > 0, ∀ N, (F N : ℝ) ≥ C * (N : ℝ) ^ (1 / 2 - ε) := by
  sorry

end Erdos131
