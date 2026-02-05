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
# Erdős Problem 574

For k ≥ 2, is it true that ex(n; {C_{2k-1}, C_{2k}}) = (1+o(1))(n/2)^{1+1/k}?
This asks for the precise asymptotic of the Turán number when forbidding consecutive cycle lengths.

OPEN

*Reference:* [erdosproblems.com/574](https://www.erdosproblems.com/574)
-/

open SimpleGraph Asymptotics

open scoped Topology Real

namespace Erdos574

variable {α : Type*}

/-- The Turán number ex(n; F): maximum edges avoiding all forbidden subgraphs -/
noncomputable def extremalNumber (n : ℕ) (forbidden : ∀ {β : Type*}, SimpleGraph β → Prop) : ℕ := sorry

/-- The cycle graph on m vertices -/
def cycleGraph (m : ℕ) : SimpleGraph (Fin m) := sorry

/-- Predicate: graph avoids C_{2k-1} and C_{2k} -/
def avoidsConsecutiveCycles (k : ℕ) {β : Type*} (G : SimpleGraph β) : Prop :=
  (∀ (f : Fin (2*k-1) ↪ β), ¬ sorry) ∧  -- no (2k-1)-cycle
  (∀ (f : Fin (2*k) ↪ β), ¬ sorry)      -- no 2k-cycle

/-- Conjecture: ex(n; {C_{2k-1}, C_{2k}}) = (1+o(1))(n/2)^{1+1/k} for k ≥ 2 -/
@[category research open, AMS 05]
theorem extremal_consecutive_cycles (k : ℕ) (hk : k ≥ 2) (answer : Prop) :
    answer ↔ (fun (n : ℕ) => (extremalNumber n (fun G => avoidsConsecutiveCycles k G) : ℝ)) ~[Filter.atTop]
      (fun n => ((n : ℝ) / 2) ^ (1 + 1 / (k : ℝ))) := by
  sorry

end Erdos574
