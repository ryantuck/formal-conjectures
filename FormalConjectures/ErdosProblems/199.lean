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
import Mathlib.Data.Real.Basic
import FormalConjectures.Util.ProblemImports

open BigOperators

namespace Erdos199

open Set

/--
A set $A \subset \mathbb{R}$ does not contain a 3-term arithmetic progression.
-/
def HasNoThreeTermAP (A : Set ℝ) : Prop :=
  ∀ x y z, x ∈ A → y ∈ A → z ∈ A → x + z = 2 * y → x = y

/--
A set $S \subset \mathbb{R}$ contains an infinite arithmetic progression.
-/
def HasInfiniteAP (S : Set ℝ) : Prop :=
  ∃ a d : ℝ, d ≠ 0 ∧ ∀ n : ℕ, a + n * d ∈ S

/--
If $A\subset \mathbb{R}$ does not contain a 3-term arithmetic progression then must $\mathbb{R}\backslash A$ contain an infinite arithmetic progression?
-/
@[category research solved, AMS 11]
theorem erdos_problem_199 :
    ¬ (∀ A : Set ℝ, HasNoThreeTermAP A → HasInfiniteAP (Aᶜ)) :=
  sorry

end Erdos199
