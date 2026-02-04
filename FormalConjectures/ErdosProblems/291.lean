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
# Erdős Problem 291

*Reference:* [erdosproblems.com/291](https://www.erdosproblems.com/291)
-/

open Filter Topology

namespace Erdos291

/--
Let $n \geq 1$ and define $L_n$ as the least common multiple of $\{1, \ldots, n\}$
and $a_n$ by: $\sum_{1 \leq k \leq n} \frac{1}{k} = \frac{a_n}{L_n}$.

Question: Is it true that both $(a_n, L_n) = 1$ and $(a_n, L_n) > 1$ occur
for infinitely many $n$?
-/
noncomputable def L (n : ℕ) : ℕ := (Finset.range n).lcm id

noncomputable def a (n : ℕ) : ℚ :=
  (Finset.range n).sum (fun k => (1 : ℚ) / (k + 1))

/--
Main question: Do both $(a_n, L_n) = 1$ and $(a_n, L_n) > 1$ occur infinitely often?
-/
@[category research open, AMS 11]
theorem erdos_291 :
    (Set.Infinite {n : ℕ | (a n).num.gcd (L n) = 1}) ∧
    (Set.Infinite {n : ℕ | (a n).num.gcd (L n) > 1}) := by
  sorry

/--
Wu-Yan (2022): Assuming $\frac{1}{\log p}$ linear independence over $\mathbb{Q}$,
the set where $(a_n, L_n) > 1$ has upper density 1.
-/
@[category research open, AMS 11]
theorem erdos_291.wu_yan_conditional :
    -- Conditional on linear independence assumption
    let S := {n : ℕ | (a n).num.gcd (L n) > 1}
    limsup (fun N : ℕ => (Finset.range N).card / (N : ℝ) -
      ((Finset.range N).filter (fun n => (a n).num.gcd (L n) = 1)).card / (N : ℝ)) atTop = 1 := by
  sorry

end Erdos291
