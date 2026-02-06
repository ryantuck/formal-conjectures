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
# Erdős Problem 883

Coprimality graph contains odd cycles.

OPEN

*Reference:* [erdosproblems.com/883](https://www.erdosproblems.com/883)
-/

open Finset Nat

open scoped Topology Real

namespace Erdos883

/-- Coprimality graph -/
def coprimalityGraph (A : Finset ℕ) : SimpleGraph ℕ := sorry

/-- Large subsets have coprimality graph with odd cycles -/
@[category research open, AMS 05]
theorem coprimality_graph_odd_cycles (n : ℕ) (answer : Prop) :
    answer ↔ ∀ (A : Finset ℕ),
      A ⊆ Finset.range (n + 1) →
      A.card > Nat.floor (n / 2) + Nat.floor (n / 3) - Nat.floor (n / 6) →
      sorry := by
  sorry

end Erdos883
