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
# Erdős Problem 619

For connected triangle-free graph G, does there exist c > 0 such that h₄(G) < (1-c)n?

OPEN

*Reference:* [erdosproblems.com/619](https://www.erdosproblems.com/619)
-/

open SimpleGraph

open scoped Topology Real

namespace Erdos619

variable {α : Type*} [Fintype α]

/-- h_r(G): min edges to add for diameter r while staying triangle-free -/
noncomputable def h_r (r : ℕ) (G : SimpleGraph α) : ℕ := sorry

/-- ∃ c > 0 such that h₄(G) < (1-c)n for connected triangle-free G -/
@[category research open, AMS 05]
theorem h4_linear_improvement (answer : Prop) :
    answer ↔ ∃ c > 0, ∀ᶠ (n : ℕ) in Filter.atTop,
      ∀ (G : SimpleGraph (Fin n)),
        G.Connected →
        (∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj a c) →
        h_r 4 G < Nat.floor ((1 - c) * n) := by
  sorry

end Erdos619
