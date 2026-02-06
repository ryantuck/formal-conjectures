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
# Erdős Problem 726

Residue class sum conjecture: ∑_{p≤n} 1/p ~ (log log n)/2.

OPEN

*Reference:* [erdosproblems.com/726](https://www.erdosproblems.com/726)
-/

open Finset Nat

open scoped Topology Real BigOperators

namespace Erdos726

/-- Sum over primes in residue classes -/
noncomputable def S (n : ℕ) : ℝ :=
  ∑ p in (Finset.range (n+1)).filter Nat.Prime, (1 : ℝ) / p

/-- Residue class sum conjecture -/
@[category research open, AMS 11]
theorem residue_class_sum :
    Filter.Tendsto (fun n => S n / (Real.log (Real.log n) / 2))
      Filter.atTop (nhds 1) := by
  sorry

end Erdos726
