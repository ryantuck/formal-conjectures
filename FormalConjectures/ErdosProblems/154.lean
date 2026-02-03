/- Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
you may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import FormalConjectures.Util.ProblemImports

/-! # Erdős Problem 154

*Reference:* [erdosproblems.com/154](https://www.erdosproblems.com/154)
-/

open Filter Set Finset Asymptotics Topology

open scoped Pointwise

namespace Erdos154

/--
Let $A\subset \{1,\ldots,N\}$ be a Sidon set with $\lvert A\rvert\sim N^{1/2}$. Must $A+A$ be
well-distributed over all small moduli? In particular, must about half the elements of $A+A$ be
even and half odd?

The problem has been solved in the affirmative.
Lindström [Li98] has shown that the property of being well-distributed is true for $A$ itself.
It is noted that this property for $A+A$ follows immediately using the Sidon property.

[ESS94] P. Erdős, A. Sárközy, and V. T. Sós, "On sumsets of Sidon sets. I", J. Number Theory 47 (1994), 329–347.
[Li98] B. Lindström, "On the distribution of Sidon sets", Discrete Math. 186 (1998), 279–281.
[Ko99] M. N. Kolountzakis, "The density of Sidon sets and the distribution of their sums", Acta Arith. 89 (1999), 115–127.
-/ 
@[category research solved, AMS 11] 
theorem erdos_154 : answer(True) ↔
    ∀ (m : ℕ) (r : ℕ), m > 0 → r < m →
    ∀ (A : ℕ → Finset ℕ),
    (∀ N, A N ⊆ Icc 1 N) →
    (∀ N, IsSidon (A N)) →
    ((fun N ↦ ((A N).card : ℝ)) ~[atTop] (fun N ↦ Real.sqrt N)) →
    Tendsto (fun N ↦ (((A N + A N).filter (fun x ↦ x % m = r)).card : ℝ) / ((A N + A N).card : ℝ)) atTop (𝓝 (1 / m)) :=
  sorry

end Erdos154