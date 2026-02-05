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
# Erdős Problem 521

Let (ε_k) be independently uniformly chosen from {-1,1}. For f_n(z)=∑_{0≤k≤n} ε_k z^k,
does the number of real roots R_n satisfy: almost surely, lim_{n→∞} R_n/log n = 2/π?

OPEN

*Reference:* [erdosproblems.com/521](https://www.erdosproblems.com/521)
-/

open MeasureTheory ProbabilityTheory Real Polynomial Filter Topology

namespace Erdos521

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- Real roots of random polynomials grow like (2/π) log n -/
@[category research open, AMS 60]
theorem random_polynomial_real_roots
    (eps : ℕ → Ω → Fin 2)
    (h_indep : iIndepFun eps ℙ)
    (h_unif : ∀ k, ℙ {ω | eps k ω = 0} = 1/2 ∧ ℙ {ω | eps k ω = 1} = 1/2) :
    ∀ᵐ ω ∂ℙ,
      let f : ℕ → Polynomial ℝ := fun n =>
        ∑ k ∈ Finset.range (n + 1), (if eps k ω = 0 then -1 else 1 : ℝ) • X ^ k
      Tendsto (fun n => (Nat.card {x : ℝ | (f n).eval x = 0}) / log n)
        atTop (𝓝 (2 / π)) := by
  sorry

end Erdos521
