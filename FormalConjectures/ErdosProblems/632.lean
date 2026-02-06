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
# Erdős Problem 632

If a graph G is (a,b)-choosable, must it be (am,bm)-choosable for all m ≥ 1?

DISPROVED by counterexample of Dvořák et al.

*Reference:* [erdosproblems.com/632](https://www.erdosproblems.com/632)
-/

open SimpleGraph

open scoped Topology Real

namespace Erdos632

variable {α : Type*}

/-- A graph is (a,b)-choosable -/
def IsChoosable (a b : ℕ) (G : SimpleGraph α) : Prop := sorry

/-- Negation: (a,b)-choosable does not imply (am,bm)-choosable -/
@[category research solved, AMS 05]
theorem not_choosable_multiplication :
    ¬ ∀ (a b : ℕ) (G : SimpleGraph α),
      IsChoosable a b G →
      ∀ m : ℕ, m ≥ 1 → IsChoosable (a*m) (b*m) G := by
  sorry

end Erdos632
