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
# Erdős Problem 926

Extremal number of graph H_k.

PROVED

*Reference:* [erdosproblems.com/926](https://www.erdosproblems.com/926)
-/

open Finset

open scoped Topology Real

namespace Erdos926

variable {α β : Type*}

/-- Graph H_k structure (k disjoint paths of length k) - simplified formulation -/
def H_k_free {α : Type*} [DecidableEq α] (k : ℕ) (G : SimpleGraph α) : Prop :=
  ∀ (paths : Fin k → List α),
    (∀ i, (paths i).length = k + 1) →
    (∀ i j, i ≠ j → (paths i).toFinset ∩ (paths j).toFinset = ∅) →
    ¬(∀ i, ∀ j (hj : j + 1 < (paths i).length), G.Adj ((paths i)[j]'(Nat.lt_of_succ_lt hj)) ((paths i)[j + 1]'hj))

/-- Extremal number for H_k-free graphs -/
@[category research solved, AMS 05]
theorem extremal_h_k (k : ℕ) :
    ∃ (c : ℝ), 0 < c ∧
      ∀ (n : ℕ), ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        H_k_free k G → c * (n : ℝ) ^ (3/2) ≤ G.edgeFinset.card := by
  sorry

end Erdos926
