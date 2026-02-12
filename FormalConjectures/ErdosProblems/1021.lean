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
# Erdős Problem 1021

Bipartite graph extremal number.

PROVED

STATUS: SOLVED

*Reference:* [erdosproblems.com/1021](https://www.erdosproblems.com/1021)
-/

open Finset

open scoped Topology Real

namespace Erdos1021

variable {α β : Type*}

/-- English version: Extremal number for 1-subdivision of K_k -/@[category research solved, AMS 05]
theorem subdivision_extremal (k : ℕ) :
    ∃ (c : ℝ), 0 < c ∧
      ∀ (n : ℕ) (G : SimpleGraph α) [Fintype α] [DecidableRel G.Adj],
        Fintype.card α = n →
        (∀ H : SimpleGraph α, H ≤ G → ∃ m, m ≠ k) →
        (G.edgeFinset.card : ℝ) ≤ (n : ℝ) ^ (3/2 - c) := by
  sorry

end Erdos1021
