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
# Erdős Problem 720

Size Ramsey number for paths and cycles.

PROVED ($100 reward)

*Reference:* [erdosproblems.com/720](https://www.erdosproblems.com/720)
-/

open Finset

open scoped Topology Real

namespace Erdos720

variable {α : Type*}

/-- Size Ramsey number -/
noncomputable def sizeRamsey (G : SimpleGraph α) : ℕ := sorry

/-- Path graph on n vertices -/
def pathGraph (n : ℕ) : SimpleGraph (Fin n) := sorry

/-- Cycle graph on n vertices -/
def cycleGraph (n : ℕ) : SimpleGraph (Fin n) := sorry

/-- Size Ramsey number for paths is linear -/
@[category research solved, AMS 05]
theorem size_ramsey_path :
    ∃ C : ℝ, C > 0 ∧
      ∀ n : ℕ, sizeRamsey (pathGraph n) ≤ C * n := by
  sorry

/-- Size Ramsey number for cycles is linear -/
@[category research solved, AMS 05]
theorem size_ramsey_cycle :
    ∃ C : ℝ, C > 0 ∧
      ∀ n : ℕ, sizeRamsey (cycleGraph n) ≤ C * n := by
  sorry

end Erdos720
