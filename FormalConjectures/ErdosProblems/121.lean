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
# Erdős Problem 121

*Reference:* [erdosproblems.com/121](https://www.erdosproblems.com/121)
-/

namespace Erdos121

open Finset Filter Real Classical

/--
The property that no `k` distinct elements of `A` have a product that is a square.
-/
def NoProductKIsSquare (A : Finset ℕ) (k : ℕ) : Prop :=
  ∀ S ⊆ A, S.card = k → ¬ IsSquare (S.prod id)

/--
`F_k(N)` is the size of the largest subset of `{1, ..., N}` such that no `k` distinct elements
have a product that is a square.
-/
noncomputable def F (k N : ℕ) : ℕ :=
  sup (filter (fun A => A ⊆ Icc 1 N ∧ NoProductKIsSquare A k) (powerset (Icc 1 N))) card

/--
Erdős, Sós, and Sárközy conjectured that $F_{2k+1}(N) = (1 - o(1))N$.
Tao [Ta24] proved this is false for all odd $k \ge 5$ (in fact for all $k \ge 4$, even or odd).
-/
@[category research solved, AMS 11]
theorem erdos_121 :
    answer(False) ↔ ∀ k ≥ 2, Tendsto (fun N ↦ (F (2 * k + 1) N : ℝ) / N) atTop (nhds 1) := by
  sorry

end Erdos121
