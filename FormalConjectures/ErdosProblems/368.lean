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
# Erdős Problem 368

Let $F(n)$ denote the largest prime factor of $n(n+1)$. How large is $F(n)$?

Known results:
- Pólya: $F(n) \to \infty$
- Mahler: $F(n) \gg \log \log n$
- Schinzel: For infinitely many n, $F(n) \leq n^{O(1/\log \log \log n)}$
- Pasten (2024): $F(n) \gg (\log \log n)^2/\log \log \log n$

Erdős conjectured: For every $\epsilon > 0$, infinitely many n with $F(n) < (\log n)^{2+\epsilon}$.

*Reference:* [erdosproblems.com/368](https://www.erdosproblems.com/368)
-/

open Filter Topology BigOperators Real

namespace Erdos368

/-- Largest prime factor of n(n+1) -/
noncomputable def F (n : ℕ) : ℕ :=
  sSup {p : ℕ | p.Prime ∧ p ∣ n * (n + 1)}

/-- Pólya: F(n) → ∞ -/
@[category research solved, AMS 11]
theorem erdos_368_polya :
    Tendsto F atTop atTop := by
  sorry

/-- Pasten (2024): Lower bound -/
@[category research solved, AMS 11]
theorem erdos_368_pasten :
    ∃ c : ℝ, c > 0 ∧ ∀ᶠ n : ℕ in atTop,
      (F n : ℝ) ≥ c * (log (log n))^2 / log (log (log n)) := by
  sorry

/-- Erdős's conjecture: Upper bound for infinitely many n -/
def erdos_368_conjecture : Prop :=
  ∀ ε > 0, ∃ᶠ n : ℕ in atTop, (F n : ℝ) < (log n)^(2 + ε)

end Erdos368
