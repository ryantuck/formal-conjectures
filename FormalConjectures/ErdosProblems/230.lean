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
# Erdős Problem 230

*Reference:* [erdosproblems.com/230](https://www.erdosproblems.com/230)
-/

open Complex Filter Topology

namespace Erdos230

/--
Let $P(z)=\sum_{1\leq k\leq n}a_kz^k$ for some $a_k\in \mathbb{C}$ with $|a_k|=1$
for $1\leq k\leq n$. Does there exist a constant $c>0$ such that, for $n\geq 2$,
we have $\max_{|z|=1}|P(z)| \geq (1+c)\sqrt{n}$?

This was disproved by Kahane [Ka80], who constructed 'ultraflat' polynomials
with $P(z)=(1+o(1))\sqrt{n}$ uniformly for all $z$ with $|z|=1$.

[Ka80] Kahane, J.-P., _Sur les polynômes à coefficients unimodulaires_.
  Bull. London Math. Soc. (1980), 321-342.
-/
@[category research solved, AMS 30]
theorem erdos_230 : ¬ ∃ c > 0, ∀ n : ℕ, n ≥ 2 → ∀ a : Fin (n + 1) → ℂ,
    (∀ k, norm (a k) = 1) →
    let P := fun z => ∑ k : Fin (n + 1), if k.val = 0 then 0 else a k * z^(k.val : ℕ)
    (⨆ z : ℂ, if norm z = 1 then norm (P z) else 0) ≥ (1 + c) * Real.sqrt (n : ℝ) := by
  sorry

/--
Kahane's ultraflat polynomials achieve $P(z)=(1+o(1))\sqrt{n}$ uniformly on the unit circle.
-/
@[category research solved, AMS 30]
theorem erdos_230.kahane_ultraflat : ∀ ε > 0, ∃ N, ∀ n : ℕ, n ≥ N →
    ∃ a : Fin (n + 1) → ℂ, (∀ k, norm (a k) = 1) ∧
      let P := fun z => ∑ k : Fin (n + 1), if k.val = 0 then 0 else a k * z^(k.val : ℕ)
      ∀ z : ℂ, norm z = 1 →
        norm (P z) ≤ (1 + ε) * Real.sqrt (n : ℝ) ∧
        norm (P z) ≥ (1 - ε) * Real.sqrt (n : ℝ) := by
  sorry

end Erdos230
