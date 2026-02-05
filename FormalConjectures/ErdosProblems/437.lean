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
# Erdős Problem 437

Given a strictly increasing sequence 1 ≤ a₁ < ... < aₖ ≤ x, how many of the partial
products a₁, a₁a₂, ..., a₁···aₖ can be perfect squares? Is it true that for any ε > 0,
there can exist more than x^(1-ε) such squares?

Bui-Pratt-Zaharescu (2024): PROVED - If L(x) denotes the maximum number of such squares
and u(x) = (log x log log x)^(1/2), then:
  x·exp(-(√2 + o(1))u(x)) ≤ L(x) ≤ x·exp(-(1/√2 + o(1))u(x))

*Reference:* [erdosproblems.com/437](https://www.erdosproblems.com/437)
-/

open Filter Topology BigOperators Real

namespace Erdos437

/-- L(x) is the maximum number of square partial products -/
noncomputable def L (x : ℝ) : ℕ :=
  sSup {n : ℕ | ∃ (seq : ℕ → ℕ), StrictMono seq ∧ (∀ i < n, (seq i : ℝ) ≤ x) ∧
    ∀ i < n, ∃ k : ℕ, (Finset.range (i + 1)).prod (fun j => seq j) = k ^ 2}

/-- Bui-Pratt-Zaharescu: Bounds on L(x) -/
@[category research solved, AMS 11]
theorem erdos_437_bui_pratt_zaharescu :
    ∀ᶠ x : ℝ in atTop,
      let u := (log x * log (log x)) ^ ((1:ℝ)/2)
      x * exp (-(2 : ℝ) ^ ((1:ℝ)/2) * u) ≤ (L x : ℝ) ∧
      (L x : ℝ) ≤ x * exp (-(2 : ℝ) ^ (-(1:ℝ)/2) * u) := by
  sorry

end Erdos437
