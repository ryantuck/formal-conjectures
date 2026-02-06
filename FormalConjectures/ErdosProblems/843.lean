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
# Erdős Problem 843

Squares are Ramsey 2-complete.

SOLVED

*Reference:* [erdosproblems.com/843](https://www.erdosproblems.com/843)
-/

open Finset

open scoped Topology Real

namespace Erdos843

/-- Squares are Ramsey 2-complete -/
@[category research solved, AMS 11]
theorem squares_ramsey_complete :
    ∀ (c : Fin 2 → Set ℕ),
      (∀ k : ℕ, ∃ i : Fin 2, k ^ 2 ∈ c i) →
      ∀ (N : ℕ), ∃ (i : Fin 2) (S : Finset ℕ),
        (∀ s ∈ S, ∃ k : ℕ, s = k ^ 2) ∧
        (∀ s ∈ S, s ∈ c i) ∧
        ∀ n ≥ N, ∃ T ⊆ S, sorry := by
  sorry

end Erdos843
