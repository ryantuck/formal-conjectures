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
# Erdős Problem 524

For t ∈ (0,1) with binary expansion t = ∑ ε_k(t)2^{-k}, determine the order of magnitude
of M_n(t) = max_{x ∈ [-1,1]} |∑_{k≤n} (-1)^{ε_k(t)} x^k| for almost all t.

OPEN with partial results by Chung and Erdős.

*Reference:* [erdosproblems.com/524](https://www.erdosproblems.com/524)
-/

open Real MeasureTheory Filter BigOperators Topology

namespace Erdos524

/-- Order of magnitude of M_n for binary expansion coefficients -/
@[category research open, AMS 60]
theorem binary_expansion_polynomial_max :
    ∃ (c : ℝ), c > 0 ∧ ∀ᵐ (t : ℝ) ∂volume.restrict (Set.Ioo 0 1),
      ∃ (eps : ℕ → Fin 2), (∀ k, (eps k : ℝ) = ⌊t * 2^(k+1)⌋ - 2 * ⌊t * 2^k⌋) →
        Tendsto (fun n =>
          (⨆ (x : ℝ) (hx : x ∈ Set.Icc (-1:ℝ) 1),
            |∑ k ∈ Finset.range (n + 1), (-1 : ℝ) ^ (eps k : ℕ) * x ^ k|) /
          Real.sqrt n) atTop (𝓝 c) := by
  sorry

end Erdos524
