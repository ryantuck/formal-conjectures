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
# Erdős Problem 783

Largest primes minimize nondivisibility count.

OPEN

*Reference:* [erdosproblems.com/783](https://www.erdosproblems.com/783)
-/

open Finset Nat

open scoped Topology Real BigOperators

namespace Erdos783

/-- Count integers not divisible by any element of A -/
noncomputable def nondivisibilityCount (A : Finset ℕ) (n : ℕ) : ℕ := sorry

/-- Largest k primes minimize nondivisibility -/
@[category research open, AMS 11]
theorem largest_primes_minimize (C : ℝ) (k n : ℕ) (answer : Prop) :
    answer ↔ ∀ (A : Finset ℕ),
      A ⊆ Finset.range (n + 1) \ {0, 1} →
      (∑ a in A, (1 : ℝ) / a) ≤ C →
      nondivisibilityCount A n ≥ sorry := by
  sorry

end Erdos783
