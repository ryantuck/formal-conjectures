/-
Copyright 2025 The Formal Conjectures Authors.

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
# Erdős Problem 452

Let ω(n) denote the count of distinct prime factors of n. Determine the size of the
largest interval I ⊆ [x, 2x] such that ω(n) > log log n for all n ∈ I.

Erdős: Integers with ω(n) > log log n have density 1/2.
CRT: Interval exists with length at least (1+o(1)) log x / (log log x)².
Conjecture: Intervals of length (log x)^k may exist for arbitrarily large k.

*Reference:* [erdosproblems.com/452](https://www.erdosproblems.com/452)
-/

open Filter Topology BigOperators Real Classical

namespace Erdos452

/-- Maximum interval length with ω(n) > log log n -/
noncomputable def maxIntervalLength (x : ℝ) : ℝ :=
  sSup {len : ℝ | ∃ a : ℕ, (x : ℝ) ≤ a ∧ (a : ℝ) + len ≤ 2*x ∧
    ∀ n : ℕ, a ≤ n ∧ n < a + ⌊len⌋₊ → (n.primeFactors.card : ℝ) > log (log n)}

/-- CRT lower bound -/
@[category research open, AMS 11]
theorem erdos_452_crt_bound :
    ∀ᶠ x : ℝ in atTop,
      maxIntervalLength x ≥ (log x / (log (log x))^2) / 2 := by
  sorry

end Erdos452
