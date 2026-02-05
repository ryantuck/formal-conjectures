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
# Erdős Problem 569

*Reference:* [erdosproblems.com/569](https://www.erdosproblems.com/569)

## Statement (OPEN)
Let k ≥ 1. Determine the best possible constant c_k such that:
R(C_{2k+1}, H) ≤ c_k m
for any graph H on m edges without isolated vertices.

This concerns the Ramsey number for odd cycles versus arbitrary graphs.

## Source
[EFRS93], Problem #34 in Ramsey Theory
-/

open SimpleGraph

open scoped Topology Real

namespace Erdos569

variable {α β : Type*}

/-- Ramsey number R(G,H) -/
def ramseyNumber (G : SimpleGraph α) (H : SimpleGraph β) : ℕ := sorry

/-- The cycle graph on n vertices -/
def cycleGraph (n : ℕ) : SimpleGraph (Fin n) := sorry

/-- Main problem: Find best constant c_k for R(C_{2k+1}, H) ≤ c_k m -/
@[category research open, AMS 05]
theorem ramsey_odd_cycle_constant (k : ℕ) (hk : k ≥ 1) :
    ∃ c : ℝ, c > 0 ∧
    (∀ c' : ℝ, c' < c →
      ∃ (H : SimpleGraph β) (m : ℕ),
        H.edgeSet.ncard = m ∧
        (∀ v, ∃ w, H.Adj v w) ∧
        (ramseyNumber (cycleGraph (2*k+1)) H : ℝ) > c' * m) ∧
    (∀ (H : SimpleGraph β) (m : ℕ),
      H.edgeSet.ncard = m →
      (∀ v, ∃ w, H.Adj v w) →
      (ramseyNumber (cycleGraph (2*k+1)) H : ℝ) ≤ c * m) :=
  sorry

end Erdos569
