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
# Erdős Problem 963

Dissociated subsets.

OPEN

*Reference:* [erdosproblems.com/963](https://www.erdosproblems.com/963)
-/

open Finset Filter

open scoped Topology Real

namespace Erdos963

/-- A set is dissociated if all subset sums are distinct -/
def IsDissociated (A : Finset ℝ) : Prop :=
  ∀ S T : Finset ℝ, S ⊆ A → T ⊆ A → S.sum id = T.sum id → S = T

/-- Maximum dissociated subset size -/
noncomputable def f (n : ℕ) : ℕ := sorry

/-- Estimate for f(n) -/
@[category research open, AMS 11]
theorem dissociated_subset_size (answer : Prop) :
    answer ↔ ∃ (g : ℕ → ℝ),
      Tendsto (fun n => (f n : ℝ) / g n) atTop (nhds 1) := by
  sorry

end Erdos963
