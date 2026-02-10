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
# Erdős Problem 929

Prime factor gaps and smooth integers.

OPEN

*Reference:* [erdosproblems.com/929](https://www.erdosproblems.com/929)
-/

open Finset Filter

open scoped Topology Real

namespace Erdos929

/-- Largest prime factor of n -/
noncomputable def largestPrimeFactor (n : ℕ) : ℕ :=
  if h : n.primeFactors.Nonempty then n.primeFactors.max' h else 1

/-- Growth of gap between largest prime factors -/
@[category research open, AMS 11]
theorem prime_factor_gap (answer : Prop) :
    answer ↔ Tendsto (fun n =>
      |((largestPrimeFactor n : ℝ) - largestPrimeFactor (n + 1))| / Real.log n)
      atTop atTop := by
  sorry

end Erdos929
