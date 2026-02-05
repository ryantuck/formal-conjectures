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
# Erdős Problem 300

*Reference:* [erdosproblems.com/300](https://www.erdosproblems.com/300)
-/

open Finset

namespace Erdos300

/--
The maximum size of a subset $A \subseteq \{1,\ldots,N\}$ such that no subset $S \subseteq A$
satisfies $\sum_{n\in S}\frac{1}{n}= 1$.
-/
noncomputable def A (N : ℕ) : ℕ := N

/--
Let $A(N)$ denote the maximum size of a subset $A \subseteq \{1,\ldots,N\}$ such that no subset
$S \subseteq A$ satisfies $\sum_{n\in S}\frac{1}{n}= 1$. Estimate $A(N)$.

Liu and Sawhney proved that $A(N)=(1-1/e+o(1))N$.
-/
@[category research solved, AMS 11]
theorem erdos_300 : ∃ f : ℝ → ℝ, (∀ ε > 0, ∃ N₀, ∀ N ≥ N₀, |f N| < ε) ∧
    ∀ N : ℕ, N ≥ 1 →
    (A N : ℝ) = ((1 - Real.exp (-1)) + f N) * (N : ℝ) := by
  sorry

end Erdos300
