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
# Erdős Problem 743

Tree packing conjecture (Gyárfás).

OPEN

*Reference:* [erdosproblems.com/743](https://www.erdosproblems.com/743)
-/

open Finset

open scoped Topology Real

namespace Erdos743

variable {α : Type*}

/-- Tree packing conjecture -/
@[category research open, AMS 05]
theorem tree_packing (n : ℕ) (answer : Prop) :
    answer ↔ ∀ (T : Fin (n-1) → SimpleGraph α),
      (∀ k : Fin (n-1), (T k).IsTree) →
      (∀ k : Fin (n-1), sorry) →
      ∃ (packing : Fin (n-1) → Set (Sym2 (Fin n))),
        sorry := by
  sorry

end Erdos743
