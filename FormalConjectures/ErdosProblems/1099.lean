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
# Erdős Problem 1099

Is it true that $\liminf_{n\to \infty}h_\alpha(n) \ll_\alpha 1$?
Where $1=d_1<\cdots<d_{\tau(n)}=n$ are the divisors of $n$, and for $\alpha>1$,
\[h_\alpha(n) = \sum_{i=1}^{\tau(n)-1} \left( \frac{d_{i+1}}{d_i}-1\right)^\alpha.\]

STATUS: OPEN

*Reference:* [erdosproblems.com/1099](https://www.erdosproblems.com/1099)
-/

open Filter

open scoped Topology Real

namespace Erdos1099

/-- Sum of divisor gap powers: $h_\alpha(n) = \sum_{i=1}^{\tau(n)-1} (\frac{d_{i+1}}{d_i}-1)^\alpha$. -/
noncomputable def h (α : ℝ) (n : ℕ) : ℝ :=
  let ds := n.divisors.sort (· ≤ ·)
  (List.zip ds ds.tail).map (fun (d1, d2) => ((d2 : ℝ) / d1 - 1) ^ α) |>.sum

/-- Liminf of divisor gap function is bounded.
    The problem asks if $\liminf_{n \to \infty} h_\alpha(n) \ll_\alpha 1$. -/
@[category research open, AMS 11]
theorem divisor_gap_bound (α : ℝ) (hα : 1 < α) :
    ∃ (C : ℝ),  atTop.liminf (fun n => h α n) ≤ C := by
  sorry

end Erdos1099
