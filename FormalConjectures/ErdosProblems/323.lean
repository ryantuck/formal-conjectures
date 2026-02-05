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
# Erdős Problem 323

Let $1 \leq m \leq k$ and $f_{k,m}(x)$ denote the count of integers $\leq x$ expressible
as sums of $m$ nonnegative $k$-th powers.

Question 1: Does $f_{k,k}(x) \gg_\epsilon x^{1-\epsilon}$ hold for all $\epsilon > 0$?
Question 2: For $m < k$, does $f_{k,m}(x) \gg x^{m/k}$ hold for sufficiently large $x$?

Landau solved k=2 case: $f_{2,2}(x) \sim cx/\sqrt{\log x}$.
For k > 2, it remains unknown whether $f_{k,k}(x) = o(x)$.

*Reference:* [erdosproblems.com/323](https://www.erdosproblems.com/323)
-/

open Filter Topology BigOperators Real

namespace Erdos323

/-- Count of integers ≤ x expressible as sum of m nonnegative k-th powers -/
noncomputable def f (k m x : ℕ) : ℕ :=
  Nat.card {n : ℕ | n ≤ x ∧ ∃ S : Finset ℕ, S.card = m ∧ n = S.sum (fun a => a^k)}

/-- Landau's result for k=2, m=2 -/
@[category research solved, AMS 11]
theorem erdos_323_landau :
    ∃ c : ℝ, c > 0 ∧ Tendsto (fun x => (f 2 2 x : ℝ) * sqrt (log x) / x) atTop (𝓝 c) := by
  sorry

/-- Question 1: Does f_{k,k}(x) ≫_ε x^{1-ε} for all ε > 0? -/
def erdos_323_question1 (k : ℕ) : Prop :=
  ∀ ε > 0, ∃ c : ℝ, c > 0 ∧ ∀ᶠ x : ℕ in atTop, (f k k x : ℝ) ≥ c * (x : ℝ)^(1 - ε)

/-- Question 2: For m < k, does f_{k,m}(x) ≫ x^{m/k}? -/
def erdos_323_question2 (k m : ℕ) : Prop :=
  m < k → ∃ c : ℝ, c > 0 ∧ ∀ᶠ x : ℕ in atTop, (f k m x : ℝ) ≥ c * (x : ℝ)^((m : ℝ) / k)

end Erdos323
