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
# Erdős Problem 367

Let B₂(n) denote the 2-full part of n (defined as n/n', where n' is the product of primes
dividing n exactly once). For every fixed k ≥ 1, does the following bound hold?

∏_{n≤m<n+k} B₂(m) ≪ n^(2+o(1))

Or perhaps even the stronger bound: ≪_k n²?

Also: For B_r (the r-full part) where r ≥ 3, does ∏_{n≤m<n+k} B_r(m) / n^(1+ε) → ∞
for fixed r, k ≥ 2 and any ε > 0?

Key result: van Doorn observed that for k ≤ 2, the bound trivially holds as
∏_{n≤m<n+k} B₂(m) ≪ n², but this fails for all k ≥ 3, with
∏_{n≤m<n+3} B₂(m) ≫ n² log n occurring infinitely often.

*Reference:* [erdosproblems.com/367](https://www.erdosproblems.com/367)
-/

open Filter Topology BigOperators Real

namespace Erdos367

/-- The r-full part (axiomatized) -/
axiom rFullPart (r : ℕ) (n : ℕ) : ℕ

/-- The 2-full part -/
noncomputable def B₂ (n : ℕ) : ℕ := rFullPart 2 n

/-- van Doorn: Bound holds for k ≤ 2 -/
@[category research open, AMS 11]
theorem erdos_367_van_doorn_k2 (n k : ℕ) (hk : k ≤ 2) :
    (∏ m ∈ Finset.Ico n (n + k), (B₂ m : ℝ)) ≤ (n : ℝ)^2 := by
  sorry

/-- van Doorn: Bound fails for k ≥ 3 -/
@[category research open, AMS 11]
theorem erdos_367_van_doorn_k3 :
    ∀ N : ℕ, ∃ n > N, (∏ m ∈ Finset.Ico n (n + 3), (B₂ m : ℝ)) ≥ (n : ℝ)^2 * Real.log n := by
  sorry

/-- Main question: Does the bound hold for all k? -/
@[category research open, AMS 11]
theorem erdos_367_main (k : ℕ) :
    ∃ c : ℝ, ∀ᶠ n : ℕ in atTop,
      (∏ m ∈ Finset.Ico n (n + k), (B₂ m : ℝ)) ≤ c * (n : ℝ)^2 := by
  sorry

/-- Extended question for r-full parts -/
@[category research open, AMS 11]
theorem erdos_367_r_full (r k : ℕ) (hr : r ≥ 3) (hk : k ≥ 2) (ε : ℝ) (hε : ε > 0) :
    Tendsto (fun n => (∏ m ∈ Finset.Ico n (n + k), (rFullPart r m : ℝ)) / (n : ℝ)^(1 + ε))
      atTop atTop := by
  sorry

end Erdos367
