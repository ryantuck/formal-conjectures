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
# Erdős Problem 857

Sunflower lemma - estimate m(n,k).

OPEN

*Reference:* [erdosproblems.com/857](https://www.erdosproblems.com/857)
-/

open Finset

open scoped Topology Real

namespace Erdos857

/-- Sunflower -/
def IsSunflower (F : Finset (Finset α)) (k : ℕ) : Prop := sorry

/-- m(n,k): minimal m for sunflower guarantee -/
noncomputable def m (n k : ℕ) : ℕ := sorry

/-- Estimate m(n,k) -/
@[category research open, AMS 05]
theorem sunflower_bound :
    sorry := by
  sorry

end Erdos857
