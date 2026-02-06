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
# Erdős Problem 983

Smooth numbers in subsets.

OPEN

*Reference:* [erdosproblems.com/983](https://www.erdosproblems.com/983)
-/

open Finset Filter

open scoped Topology Real

namespace Erdos983

/-- Function f(k,n) for smooth number containment -/
noncomputable def f (k n : ℕ) : ℕ := sorry

/-- Asymptotic behavior of f -/
@[category research open, AMS 11]
theorem smooth_numbers_subset (answer : Prop) :
    answer ↔ Tendsto (fun n =>
      2 * (Finset.filter Nat.Prime (Finset.range (Nat.floor (Real.sqrt n)))).card -
      f ((Finset.filter Nat.Prime (Finset.range n)).card + 1) n)
      atTop atTop := by
  sorry

end Erdos983
