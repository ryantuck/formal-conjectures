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
# Erdős Problem 1035

Hypercube subgraph.

OPEN

*Reference:* [erdosproblems.com/1035](https://www.erdosproblems.com/1035)
-/

open Finset

open scoped Topology Real

namespace Erdos1035

variable {α : Type*}

/-- Dense graphs contain hypercube subgraph -/
@[category research open, AMS 05]
theorem hypercube_subgraph (n : ℕ) (answer : Prop) :
    answer ↔ ∃ (c : ℝ), 0 < c ∧ c < 1 ∧
      ∀ (G : SimpleGraph (Fin (2^n))) [DecidableRel G.Adj],
        (∀ v : Fin (2^n), (G.degree v : ℝ) > (1 - c) * (2^n : ℝ)) →
        ∃ (f : Fin (2^n) → Fin (2^n)), Function.Injective f ∧
          ∀ (i j : Fin (2^n)), sorry := by
  sorry

end Erdos1035
