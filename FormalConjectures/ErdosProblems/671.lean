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
# Erdős Problem 671

Do there exist interpolation nodes where the Lebesgue constant diverges at some point,
yet Lagrange interpolation still converges to continuous functions at some points?

OPEN ($250 reward)

*Reference:* [erdosproblems.com/671](https://www.erdosproblems.com/671)
-/

open scoped Topology Real

namespace Erdos671

/-- Lebesgue constant for interpolation nodes -/
noncomputable def lebesgueConstant (nodes : Set ℝ) (x : ℝ) : ℝ := sorry

/-- Lagrange interpolation converges -/
def lagrangeConverges (nodes : Set ℝ) (x : ℝ) : Prop := sorry

/-- Interpolation nodes with divergent Lebesgue constant but convergent Lagrange interpolation -/
@[category research open, AMS 41]
theorem interpolation_divergent_lebesgue_convergent_lagrange (answer : Prop) :
    answer ↔ ∃ (nodes : ℕ → Set ℝ),
      (∃ x : ℝ, ¬ BddAbove (Set.range (fun n => lebesgueConstant (nodes n) x))) ∧
      (∃ x : ℝ, ∃ n : ℕ, lagrangeConverges (nodes n) x) := by
  sorry

end Erdos671
