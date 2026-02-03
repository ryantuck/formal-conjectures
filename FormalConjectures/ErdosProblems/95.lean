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
import Mathlib.Geometry.Euclidean.Basic

/-!
# Erdős Problem 95

*Reference:* [erdosproblems.com/95](https://www.erdosproblems.com/95)
-/

namespace Erdos95

open scoped EuclideanGeometry

/--
Let $x_1,\ldots,x_n\in\mathbb{R}^2$ determine the set of distances $\{u_1,\ldots,u_t\}$.
Suppose $u_i$ appears as the distance between $f(u_i)$ many pairs of points. Then for all
$\epsilon>0$
$$\sum_i f(u_i)^2 \ll_\epsilon n^{3+\epsilon}.$$
-/
@[category research solved, AMS 52]
theorem erdos_95 : answer(True) ↔ ∀ (ε : ℝ), 0 < ε → ∃ (C : ℝ), ∀ (n : ℕ),
    ∀ (A : Finset (EuclideanSpace ℝ (Fin 2))), A.card = n →
    let distances := Finset.image (fun p : (EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)) ↦ dist p.1 p.2) (A.product A)
    let f (d : ℝ) := ((A.product A).filter (fun p ↦ dist p.1 p.2 = d)).card
    (∑ d ∈ distances, (f d : ℝ) ^ 2) ≤ C * (n : ℝ) ^ (3 + ε) := by
  sorry

end Erdos95
