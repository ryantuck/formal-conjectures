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
# Erdős Problem 747

Shamir's problem - random hypergraph matching.

SOLVED (threshold ≈ n log n)

*Reference:* [erdosproblems.com/747](https://www.erdosproblems.com/747)
-/

open Finset Filter

open scoped Topology Real

namespace Erdos747

/-- Threshold for vertex-disjoint edges in random 3-uniform hypergraph -/
@[category research solved, AMS 05]
theorem shamir_problem :
    ∃ c : ℝ, c > 0 ∧
      ∀ᶠ (n : ℕ) in atTop,
        ∀ (m : ℕ), m ≥ ⌊c * n * Real.log n⌋₊ →
          ∃ (H : Finset (Finset (Fin n))),
            H.card = m ∧
            (∀ e ∈ H, e.card = 3) ∧
            (∃ (M : Finset (Finset (Fin n))),
              M ⊆ H ∧ M.card = n / 3 ∧
              (∀ e₁ ∈ M, ∀ e₂ ∈ M, e₁ ≠ e₂ → Disjoint e₁ e₂)) := by
  sorry

end Erdos747
