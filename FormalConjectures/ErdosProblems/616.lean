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
# Erdős Problem 616

For r-uniform hypergraphs where every induced subhypergraph on at most 3r-3 vertices
has covering number ≤ 1, determine the optimal bound t on the covering number of the
full hypergraph. Current bounds: 3r/16 + 7/8 ≤ t ≤ r/5.

OPEN

*Reference:* [erdosproblems.com/616](https://www.erdosproblems.com/616)
-/

open scoped Topology Real

namespace Erdos616

/-- r-uniform hypergraph -/
structure RUniformHypergraph (α : Type*) (r : ℕ) where
  edges : Set (Finset α)
  uniform : ∀ e ∈ edges, e.card = r

/-- Covering number (transversal number) -/
noncomputable def coveringNumber {α : Type*} {r : ℕ} (H : RUniformHypergraph α r) : ℕ := sorry

/-- Covering number bound for r-uniform hypergraphs with local covering ≤ 1 -/
@[category research open, AMS 05]
theorem covering_number_bound (r : ℕ) :
    ∃ t : ℝ, (3 * r / 16 + 7 / 8 ≤ t ∧ t ≤ r / 5) ∧
      ∀ (H : RUniformHypergraph sorry r),
        (∀ (S : Finset sorry), S.card ≤ 3*r - 3 → sorry ≤ 1) →
        (coveringNumber H : ℝ) ≤ t := by
  sorry

end Erdos616
