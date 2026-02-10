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
# Erdős Problem 890

Sum of distinct prime factors over consecutive integers.

OPEN

*Reference:* [erdosproblems.com/890](https://www.erdosproblems.com/890)
-/

open Finset Nat Filter

open scoped Topology Real BigOperators

namespace Erdos890

/-- ω(n): count of distinct prime factors of n -/
def omega (n : ℕ) : ℕ := n.primeFactors.card

/-- Question 1: liminf of sum ≤ k + π(k) -/
@[category research open, AMS 11]
theorem erdos_selfridge_liminf (k : ℕ) (hk : k ≥ 1) :
    liminf (fun n => (∑ i ∈ Finset.range k, omega (n + i) : ℝ)) atTop ≤ k + Nat.primeCounting k := by
  sorry

/-- Erdős-Selfridge lower bound: liminf ≥ k + π(k) - 1 -/
@[category research solved, AMS 11]
theorem erdos_selfridge_lower_bound (k : ℕ) (hk : k ≥ 1) :
    k + Nat.primeCounting k - 1 ≤ liminf (fun n => (∑ i ∈ Finset.range k, omega (n + i) : ℝ)) atTop := by
  sorry

/-- Question 2: limsup equals 1 -/
@[category research open, AMS 11]
theorem erdos_selfridge_limsup (k : ℕ) (hk : k ≥ 1) :
    limsup (fun n => (∑ i ∈ Finset.range k, omega (n + i) : ℝ) * Real.log (Real.log n) / Real.log n) atTop = 1 := by
  sorry

end Erdos890
