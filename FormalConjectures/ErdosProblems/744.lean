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
# Erdős Problem 744

Chromatic deletion to bipartite.

DISPROVED

*Reference:* [erdosproblems.com/744](https://www.erdosproblems.com/744)
-/

open Finset

open scoped Topology Real

namespace Erdos744

variable {α : Type*}

/-- Chromatic number -/
noncomputable def chromaticNumber (G : SimpleGraph α) : ℕ := sorry

/-- f_k(n): minimal edges to delete to make bipartite -/
noncomputable def f_k (k n : ℕ) : ℕ := sorry

/-- Disproved: f_k(n) is constant for large n -/
@[category research solved, AMS 05]
theorem chromatic_bipartite_deletion (k : ℕ) :
    ∀ᶠ (n : ℕ) in Filter.atTop,
      f_k k n = Nat.choose (k-1) 2 := by
  sorry

end Erdos744
