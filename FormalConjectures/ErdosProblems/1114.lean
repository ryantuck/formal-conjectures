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
# Erdős Problem 1114

Polynomial roots and derivative zeros.

PROVED

*Reference:* [erdosproblems.com/1114](https://www.erdosproblems.com/1114)
-/

open Finset

open scoped Real

namespace Erdos1114

/-- If f is a real polynomial whose real roots form an arithmetic progression,
    then the gaps between consecutive zeros of f', measured from the center outward,
    are monotonically increasing. Proved by Balint (1960). -/
@[category research solved, AMS 30]
theorem polynomial_derivative_zeros_monotone_gaps
    (P : Polynomial ℝ) (n : ℕ) (hn : 1 ≤ n)
    (roots : Fin (n + 2) → ℝ) (hroots_sorted : StrictMono roots)
    (hAP : ∃ d : ℝ, 0 < d ∧ ∀ i : Fin (n + 1),
      roots i.succ - roots i.castSucc = d)
    (hP_roots : ∀ i, P.IsRoot (roots i))
    (hP_deg : P.natDegree = n + 1)
    (dz : Fin (n + 1) → ℝ) (hdz_sorted : StrictMono dz)
    (hdz_roots : ∀ i, (Polynomial.derivative P).IsRoot (dz i)) :
    ∃ center : Fin n,
      ∀ i j : Fin n, i < j → j ≤ center →
        dz j.succ - dz j.castSucc ≥ dz i.succ - dz i.castSucc := by
  sorry

end Erdos1114
