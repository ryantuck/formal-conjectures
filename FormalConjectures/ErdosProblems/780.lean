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
# Erdős Problem 780

Colored hypergraph matching.

PROVED

*Reference:* [erdosproblems.com/780](https://www.erdosproblems.com/780)
-/

open Finset

open scoped Topology Real

namespace Erdos780

/-- t-colored hypergraph contains monochromatic matching -/
@[category research solved, AMS 05]
theorem colored_hypergraph_matching (r k t n : ℕ)
    (hn : n ≥ k * r + (t - 1) * (k - 1)) :
    ∀ (H : Finset (Finset (Fin n))) (c : Finset (Fin n) → Fin t),
      (∀ e ∈ H, e.card = r) →
      (∀ e₁ e₂ : Finset (Fin n), e₁ ∈ H → e₂ ∈ H →
        e₁ ∩ e₂ = ∅ → e₁ ≠ e₂ → c e₁ = c e₂ → sorry) →
      ∃ (M : Finset (Finset (Fin n))),
        M.card = k ∧
        (∀ e ∈ M, e ∈ H) ∧
        sorry := by
  sorry

end Erdos780
