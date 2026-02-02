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
# Erdős Problem 47

*Reference:* [erdosproblems.com/47](https://www.erdosproblems.com/47)
-/

namespace Erdos47

open scoped BigOperators

/--
If $\delta>0$ and $N$ is sufficiently large in terms of $\delta$, and $A\subseteq\{1,\ldots,N\}$
is such that $\sum_{a\in A}\frac{1}{a}>\delta \log N$ then must there exist $S\subseteq A$
such that $\sum_{n\in S}\frac{1}{n}=1$?

Bloom [Bl21] proved that this is true.

[Bl21] T. F. Bloom, _On a density conjecture about unit fractions_. arXiv:2112.03726 (2021).
-/
@[category research solved, AMS 11]
theorem erdos_47 : answer(True) ↔ ∀ (δ : ℝ), 0 < δ → ∃ (N₀ : ℕ), ∀ (N : ℕ), N₀ ≤ N →
    ∀ (A : Finset ℕ), ↑A ⊆ Finset.Icc 1 N →
    ∑ a ∈ A, (1 : ℝ) / a > δ * Real.log N →
    ∃ (S : Finset ℕ), S ⊆ A ∧ ∑ n ∈ S, (1 : ℚ) / n = 1 := by
  sorry

/--
Bloom [Bl21] showed that the quantitative threshold
$$\sum_{n\in A}\frac{1}{n}\gg \frac{\log\log\log N}{\log\log N}\log N$$
is sufficient.
-/
@[category research solved, AMS 11]
theorem erdos_47.variants.bloom : ∃ (C : ℝ), ∀ (N : ℕ), 2 < N →
    ∀ (A : Finset ℕ), ↑A ⊆ Finset.Icc 1 N →
    ∑ a ∈ A, (1 : ℝ) / a > C * (Real.log (Real.log (Real.log N)) / Real.log (Real.log N)) * Real.log N →
    ∃ (S : Finset ℕ), S ⊆ A ∧ ∑ n ∈ S, (1 : ℚ) / n = 1 := by
  sorry

/--
Liu and Sawhney [LiSa24] improved the threshold to
$$\sum_{n\in A}\frac{1}{n}\gg (\log N)^{4/5+o(1)}.$$

[LiSa24] H. Liu and M. Sawhney, _A proof of the density conjecture for Egyptian fractions_. arXiv:2401.03450 (2024).
-/
@[category research solved, AMS 11]
theorem erdos_47.variants.liu_sawhney : ∀ (ε : ℝ), 0 < ε → ∃ (C : ℝ), ∀ (N : ℕ), 1 < N →
    ∀ (A : Finset ℕ), ↑A ⊆ Finset.Icc 1 N →
    ∑ a ∈ A, (1 : ℝ) / a > C * (Real.log N) ^ (4 / 5 + ε) →
    ∃ (S : Finset ℕ), S ⊆ A ∧ ∑ n ∈ S, (1 : ℚ) / n = 1 := by
  sorry

end Erdos47
