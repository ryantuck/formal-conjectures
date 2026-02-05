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
# Erdős Problem 451

Estimate nₖ, the smallest integer greater than 2k such that ∏_{1≤i≤k}(nₖ-i) has
no prime factor in the interval (k, 2k).

Erdős-Graham: Proved nₖ > k^(1+c).
Erdős conjectured: nₖ < e^(o(k)) while nₖ > k^d for every constant d.
Adenwalla: Upper bound nₖ ≤ ∏_{k<p<2k} p = e^(O(k)).

*Reference:* [erdosproblems.com/451](https://www.erdosproblems.com/451)
-/

open Filter Topology BigOperators Real Classical

namespace Erdos451

/-- nₖ is the smallest integer with required property -/
noncomputable def n_k (k : ℕ) : ℕ :=
  sInf {n : ℕ | n > 2*k ∧ ∀ p : ℕ, p.Prime → k < p → p ≤ 2*k →
    ¬(p ∣ (Finset.range k).prod (fun i => n - (i + 1)))}

/-- Erdős-Graham: Lower bound -/
@[category research open, AMS 11]
theorem erdos_451_lower :
    ∃ c : ℝ, c > 0 ∧ ∀ᶠ k : ℕ in atTop,
      (n_k k : ℝ) > (k : ℝ) ^ (1 + c) := by
  sorry

/-- Adenwalla: Upper bound -/
@[category research open, AMS 11]
theorem erdos_451_upper :
    ∀ᶠ k : ℕ in atTop,
      (n_k k : ℝ) ≤ exp (10 * k) := by
  sorry

/-- Erdős conjecture: Super-polynomial lower bound -/
@[category research open, AMS 11]
theorem erdos_451_conjecture :
    ∀ d : ℝ, d > 0 → ∀ᶠ k : ℕ in atTop,
      (n_k k : ℝ) > (k : ℝ) ^ d := by
  sorry

end Erdos451
