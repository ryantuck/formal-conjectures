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
# Erdős Problem 440

Let A = {a₁ < a₂ < ...} ⊆ ℕ be an infinite sequence, and let A(x) denote the count
of indices where lcm(aᵢ, aᵢ₊₁) ≤ x.

Questions:
1. Is A(x) ≪ x^(1/2)?
2. How large can liminf A(x)/x^(1/2) be?

van Doorn: SOLVED - A(x) ≤ (c + o(1))x^(1/2) where c = ∑_{n≥1} 1/(n^(1/2)(n+1)) ≈ 1.86,
and this constant is optimal.

*Reference:* [erdosproblems.com/440](https://www.erdosproblems.com/440)
-/

open Filter Topology BigOperators Real

namespace Erdos440

/-- A(x) counts indices with small lcm -/
noncomputable def A (seq : ℕ → ℕ) (x : ℝ) : ℕ :=
  Nat.card {i : ℕ | (Nat.lcm (seq i) (seq (i + 1)) : ℝ) ≤ x}

/-- The optimal constant for van Doorn's bound -/
noncomputable def vanDoornConstant : ℝ :=
  ∑' n : ℕ, if n > 0 then 1 / ((n : ℝ) ^ ((1:ℝ)/2) * (n + 1)) else 0

/-- van Doorn: Optimal bound for A(x) -/
@[category research solved, AMS 11]
theorem erdos_440_van_doorn :
    ∀ seq : ℕ → ℕ, StrictMono seq →
      ∀ᶠ x : ℝ in atTop,
        (A seq x : ℝ) ≤ (vanDoornConstant + 1) * x ^ ((1:ℝ)/2) := by
  sorry

/-- Erdős-Szemerédi: liminf bound -/
@[category research solved, AMS 11]
theorem erdos_440_erdos_szemeredi :
    ∀ seq : ℕ → ℕ, StrictMono seq →
      liminf (fun x : ℝ => (A seq x : ℝ) / x ^ ((1:ℝ)/2)) atTop ≤ 1 := by
  sorry

end Erdos440
