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
# Erdős Problem 599

(Erdős-Menger conjecture) Let G be a (possibly infinite) graph with disjoint independent
sets A and B. Must there exist a family P of disjoint A-B paths and a set S containing
exactly one vertex from each path in P such that S intersects every A-B path?

PROVED by Aharoni and Berger (2009)

*Reference:* [erdosproblems.com/599](https://www.erdosproblems.com/599)
-/

open SimpleGraph

open scoped Topology Real

namespace Erdos599

variable {α : Type*}

/-- Erdős-Menger conjecture for infinite graphs (simplified statement) -/
@[category research solved, AMS 05]
theorem erdos_menger_conjecture (G : SimpleGraph α) (A B : Set α)
    (hdisjoint : Disjoint A B)
    (hindep_A : ∀ a₁ a₂, a₁ ∈ A → a₂ ∈ A → ¬ G.Adj a₁ a₂)
    (hindep_B : ∀ b₁ b₂, b₁ ∈ B → b₂ ∈ B → ¬ G.Adj b₁ b₂) :
    ∃ (P : Set (Σ a b, G.Walk a b)) (S : Set α),
      sorry := by
  sorry

end Erdos599
