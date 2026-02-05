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
# Erdős Problem 342

Ulam's sequence: With initial conditions a₁ = 1 and a₂ = 2, define aₙ₊₁ for n ≥ 2 as
"the least integer > aₙ which can be expressed uniquely as aᵢ + aⱼ for i < j ≤ n."

The sequence begins: 1, 2, 3, 4, 6, 8, 11, 13, 16, 18, 26, 28, ...

Questions:
1. Do infinitely many consecutive pairs of the form (a, a+2) occur?
2. Does the sequence eventually exhibit periodic differences?
3. Is the asymptotic density zero?

OPEN: All questions remain open.

*Reference:* [erdosproblems.com/342](https://www.erdosproblems.com/342)
-/

open Filter Topology BigOperators Real

namespace Erdos342

/-- Ulam's sequence (axiomatized) -/
axiom ulamSeq : ℕ → ℕ

/-- Initial conditions -/
axiom ulam_init : ulamSeq 0 = 1 ∧ ulamSeq 1 = 2

/-- Recursive definition property -/
axiom ulam_next (n : ℕ) :
    ulamSeq (n + 2) > ulamSeq (n + 1) ∧
    (∃! p : ℕ × ℕ, p.1 < p.2 ∧ p.2 ≤ n + 1 ∧
      ulamSeq p.1 + ulamSeq p.2 = ulamSeq (n + 2))

/-- Twin gaps: Do infinitely many (a, a+2) pairs occur? -/
@[category research open, AMS 11]
theorem erdos_342_twin_gaps :
    ∃ᶠ n in atTop, ulamSeq (n + 1) = ulamSeq n + 2 := by
  sorry

/-- Periodicity: Does the sequence eventually exhibit periodic differences? -/
@[category research open, AMS 11]
theorem erdos_342_periodicity :
    ∃ N p : ℕ, p > 0 ∧ ∀ n ≥ N, ulamSeq (n + p) - ulamSeq n = ulamSeq (N + p) - ulamSeq N := by
  sorry

/-- Density: Is the asymptotic density zero? -/
@[category research open, AMS 11]
theorem erdos_342_density :
    Tendsto (fun N => (Nat.card {n ∈ Set.range ulamSeq | n ≤ N} : ℝ) / N) atTop (𝓝 0) := by
  sorry

end Erdos342
