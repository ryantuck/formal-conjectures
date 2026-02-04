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
# Erdős Problem 210

*Reference:* [erdosproblems.com/210](https://www.erdosproblems.com/210)
-/

open Filter
open scoped Topology Classical

namespace Erdos210

noncomputable section

/--
The property that a set of points in $\mathbb{R}^2$ are all on a single line.
-/
def IsCollinear (P : Set (ℝ × ℝ)) : Prop :=
  ∃ (p1 p2 : ℝ × ℝ), p1 ≠ p2 ∧ P ⊆ { p | ∃ (t : ℝ), p = (1 - t) • p1 + t • p2 }

/--
The set of lines determined by pairs of points in $P$.
-/
def LinesDeterminedBy (P : Finset (ℝ × ℝ)) : Set (Set (ℝ × ℝ)) :=
  { L | ∃ p1 ∈ P, ∃ p2 ∈ P, p1 ≠ p2 ∧ L = { p | ∃ (t : ℝ), p = (1 - t) • p1 + t • p2 } }

/--
A line is ordinary for $P$ if it contains exactly two points of $P$.
-/
def IsOrdinaryLine (L : Set (ℝ × ℝ)) (P : Finset (ℝ × ℝ)) : Prop :=
  (P.filter (fun p => p ∈ L)).card = 2

/--
The number of ordinary lines in a set of points $P$.
-/
def NumOrdinaryLines (P : Finset (ℝ × ℝ)) : ℕ :=
  Set.ncard { L ∈ LinesDeterminedBy P | IsOrdinaryLine L P }

/--
$f(n)$ is the minimum number of ordinary lines over all non-collinear sets of $n$ points.
-/
def f (n : ℕ) : ℕ :=
  sInf { NumOrdinaryLines P | (P : Finset (ℝ × ℝ)) (_ : P.card = n) (_ : ¬ IsCollinear P.toSet) }

end

/--
Green and Tao [GrTa13] proved that $f(n) \ge n/2$ for sufficiently large even $n$,
and $f(n) \ge 3\lfloor n/4 floor$ for sufficiently large odd $n$.

[GrTa13] Green, B. and Tao, T., _On ordinary lines_,
Discrete & Computational Geometry (2013).
-/
@[category research solved, AMS 52]
theorem erdos_210 : ∀ᶠ (n : ℕ) in atTop,
    (Even n → (f n : ℝ) ≥ n / 2) ∧
    (Odd n → (f n : ℝ) ≥ 3 * (n / 4 : ℕ)) := by
  sorry

end Erdos210
