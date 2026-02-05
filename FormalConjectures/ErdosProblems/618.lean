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
# Erdős Problem 618

For triangle-free graph G with max degree o(√n), if h₂(G) denotes the minimum edges
needed to add to achieve diameter 2 while remaining triangle-free, must h₂(G) = o(n²)?

PROVED by Alon

*Reference:* [erdosproblems.com/618](https://www.erdosproblems.com/618)
-/

open SimpleGraph

open scoped Topology Real

namespace Erdos618

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- h₂(G): min edges to add for diameter 2 while staying triangle-free -/
noncomputable def h₂ (G : SimpleGraph α) : ℕ := sorry

/-- Max degree o(√n) implies h₂(G) = o(n²) -/
@[category research solved, AMS 05]
theorem small_degree_implies_small_h2 :
    ∀ ε > 0, ∃ δ > 0, ∀ᶠ (n : ℕ) in Filter.atTop,
      ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        (∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj a c) →
        (∀ v, (G.degree v : ℝ) ≤ δ * Real.sqrt n) →
        (h₂ G : ℝ) < ε * (n : ℝ) ^ 2 := by
  sorry

end Erdos618
