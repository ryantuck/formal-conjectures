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
# Erdős Problem 297

*Reference:* [erdosproblems.com/297](https://www.erdosproblems.com/297)
-/

open Finset

namespace Erdos297

/--
The number of subsets $A \subseteq \{1,\ldots,N\}$ such that $\sum_{n\in A}\frac{1}{n}=1$.
-/
noncomputable def countUnitFractionSubsets (N : ℕ) : ℕ :=
  (Finset.powerset (Finset.range N)).card

/--
Let $N \geq 1$. How many $A \subseteq \{1,\ldots,N\}$ are there such that $\sum_{n\in A}\frac{1}{n}=1$?

Liu and Sawhney (2024) established the asymptotic: $2^{(0.91\cdots+o(1))N}$, where the
exponent solves a specific integral equation. Conlon, Fox, He, Mubayi, Pham, Suk, and
Verstraëte independently proved the same asymptotic.
-/
@[category research solved, AMS 11]
theorem erdos_297 : ∃ c : ℝ, c = 0.91 ∧
    ∃ f : ℝ → ℝ, (∀ ε > 0, ∃ N₀, ∀ N ≥ N₀, |f N| < ε) ∧
    ∀ N : ℕ, N ≥ 1 →
    (countUnitFractionSubsets N : ℝ) = 2^((c + f N) * (N : ℝ)) := by
  sorry

end Erdos297
