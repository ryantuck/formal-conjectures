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
# Erdős Problem 211

*Reference:* [erdosproblems.com/211](https://www.erdosproblems.com/211)
-/

open Filter
open scoped Topology Classical

namespace Erdos211

noncomputable section

/--
The set of lines determined by a set of points $P \subset \mathbb{R}^2$.
A line is represented as a set of points.
-/
def LinesDeterminedBy (P : Finset (ℝ × ℝ)) : Set (Set (ℝ × ℝ)) :=
  { L | ∃ p1 ∈ P, ∃ p2 ∈ P, p1 ≠ p2 ∧ L = { p | ∃ (t : ℝ), p = (1 - t) • p1 + t • p2 } }

/--
The number of points from $P$ on a line $L$.
-/
def PointsOnLine (L : Set (ℝ × ℝ)) (P : Finset (ℝ × ℝ)) : ℕ :=
  (P.filter (fun p => p ∈ L)).card

/--
Beck [Be83] and Szemerédi-Trotter [SzTr83] proved that if at most $n-k$ points are on a line,
there are $\gg kn$ lines.

[Be83] Beck, J., _On the lattice property of the plane and some problems of Dirac, Motzkin and
Erdős in combinatorial geometry_, Combinatorica (1983).

[SzTr83] Szemerédi, E. and Trotter, W. T., _Extremal problems in discrete geometry_,
Combinatorica (1983).
-/
@[category research solved, AMS 52]
theorem erdos_211 : ∃ C > 0, ∀ (n k : ℕ), 1 ≤ k → k < n →
    ∀ (P : Finset (ℝ × ℝ)), P.card = n →
    (∀ L ∈ LinesDeterminedBy P, PointsOnLine L P ≤ n - k) →
    (Set.ncard (LinesDeterminedBy P) : ℝ) ≥ C * k * n := by
  sorry

end
end Erdos211
