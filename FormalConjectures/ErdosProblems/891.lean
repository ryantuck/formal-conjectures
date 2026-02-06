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
# Erdős Problem 891

Primorial interval with >k prime factors.

OPEN

*Reference:* [erdosproblems.com/891](https://www.erdosproblems.com/891)
-/

open Finset Nat

open scoped Topology Real

namespace Erdos891

/-- Primorial p₁···pₖ -/
def primorial (k : ℕ) : ℕ := sorry

/-- Interval contains number with >k prime factors -/
@[category research open, AMS 11]
theorem primorial_interval_many_factors (k : ℕ) (answer : Prop) :
    answer ↔ ∀ (m : ℕ),
      ∃ (n : ℕ), m < n ∧ n ≤ m + primorial k ∧
        (Finset.filter (fun p => p.Prime ∧ p ∣ n) (Finset.range (n + 1))).card > k := by
  sorry

end Erdos891
