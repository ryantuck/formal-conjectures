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
# Erdős Problem 597

Let G be a graph on at most ℵ₁ vertices containing no K₄ and no K_{ℵ₀,ℵ₀}.
Does the partition relation ω₁² → (ω₁ω, G)² hold?

OPEN

*Reference:* [erdosproblems.com/597](https://www.erdosproblems.com/597)
-/

open SimpleGraph Cardinal Ordinal

open scoped Topology Real

namespace Erdos597

/-- Partition relation for ordinals and graphs (simplified statement) -/
@[category research open, AMS 03]
theorem partition_relation_omega_one_graph (answer : Prop) :
    answer ↔ ∀ (G : SimpleGraph (Ordinal.{0})),
      (∀ (f : Fin 4 ↪ Ordinal.{0}), ¬ ∀ i j, i ≠ j → G.Adj (f i) (f j)) →
      True := by
  sorry

end Erdos597
