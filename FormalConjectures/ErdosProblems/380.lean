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
# Erdős Problem 380

An interval [u,v] is "bad" if the greatest prime factor of ∏(u≤m≤v) m appears with
exponent greater than 1. Let B(x) count integers n≤x contained in at least one bad interval.

Conjecture: Does B(x) ~ #{n≤x : P(n)²|n}, where P(n) is the largest prime factor of n?

Erdős-Graham: B(x) > x^(1-o(1)).

*Reference:* [erdosproblems.com/380](https://www.erdosproblems.com/380)
-/

open Filter Topology BigOperators Real

namespace Erdos380

/-- Largest prime factor of n -/
noncomputable def P (n : ℕ) : ℕ :=
  sSup {p : ℕ | p.Prime ∧ p ∣ n}

/-- An interval is bad if largest prime factor of product appears with exponent > 1 -/
def IsBadInterval (u v : ℕ) : Prop :=
  u ≤ v ∧ ∃ p : ℕ, p.Prime ∧
    (p = P ((Finset.Ico u (v + 1)).prod id)) ∧ p^2 ∣ ((Finset.Ico u (v + 1)).prod id)

/-- Count of integers in bad intervals -/
noncomputable def B (x : ℕ) : ℕ :=
  Nat.card {n : ℕ | n ≤ x ∧ ∃ u v : ℕ, IsBadInterval u v ∧ u ≤ n ∧ n ≤ v}

/-- Erdős-Graham: B(x) > x^(1-o(1)) -/
@[category research open, AMS 11]
theorem erdos_380_lower_bound :
    ∀ ε > 0, ∀ᶠ x : ℕ in atTop, (B x : ℝ) > (x : ℝ) ^ (1 - ε) := by
  sorry

/-- Conjecture: B(x) ~ #{n≤x : P(n)²|n} -/
def erdos_380_conjecture : Prop :=
  Tendsto (fun x => (B x : ℝ) / (Nat.card {n : ℕ | n ≤ x ∧ P n ^ 2 ∣ n}))
    atTop (𝓝 1)

end Erdos380
