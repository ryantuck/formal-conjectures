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
# Erdős Problem 573

Is it true that ex(n; {C_3, C_4}) ~ (n/2)^{3/2}? This asks whether the extremal
number for graphs avoiding both triangles and 4-cycles is asymptotically (n/2)^{3/2}.

OPEN

*Reference:* [erdosproblems.com/573](https://www.erdosproblems.com/573)
-/

open SimpleGraph Asymptotics

open scoped Topology Real

namespace Erdos573

variable {α : Type*}

/-- The Turán number ex(n; F): maximum edges in an n-vertex graph avoiding all forbidden subgraphs -/
noncomputable def extremalNumber (n : ℕ) (forbidden : ∀ {β : Type*}, SimpleGraph β → Prop) : ℕ := sorry

/-- The cycle graph on k vertices -/
def cycleGraph (k : ℕ) : SimpleGraph (Fin k) := sorry

/-- Predicate: graph avoids C_3 and C_4 -/
def avoidsC3C4 {β : Type*} (G : SimpleGraph β) : Prop :=
  (∀ (f : Fin 3 ↪ β), ¬ ∀ i j, i ≠ j → G.Adj (f i) (f j)) ∧
  (∀ (f : Fin 4 ↪ β), ¬ sorry)  -- no 4-cycle

/-- Conjecture: ex(n; {C_3, C_4}) ~ (n/2)^{3/2} -/
@[category research open, AMS 05]
theorem extremal_triangle_four_cycle (answer : Prop) :
    answer ↔ (fun (n : ℕ) => (extremalNumber n (fun G => avoidsC3C4 G) : ℝ)) ~[Filter.atTop]
      (fun n => ((n : ℝ) / 2) ^ (3 / 2)) := by
  sorry

end Erdos573
