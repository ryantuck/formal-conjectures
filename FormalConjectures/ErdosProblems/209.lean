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
# Erdős Problem 209

*Reference:* [erdosproblems.com/209](https://www.erdosproblems.com/209)
-/

namespace Erdos209

/--
A line in $\mathbb{R}^2$ defined by $ax + by = c$.
-/
structure Line where
  a : ℝ
  b : ℝ
  c : ℝ
  nonzero : a ≠ 0 ∨ b ≠ 0

def Line.contains (l : Line) (p : ℝ × ℝ) : Prop :=
  l.a * p.1 + l.b * p.2 = l.c

/--
Two lines are parallel if their normal vectors are proportional.
-/
def Line.parallel (l1 l2 : Line) : Prop :=
  l1.a * l2.b = l1.b * l2.a

/--
An arrangement of lines in $\mathbb{R}^2$ where no two lines are parallel.
-/
structure Arrangement where
  lines : Finset Line
  distinct : (lines : Set Line).Pairwise (fun l1 l2 => ¬ l1.parallel l2)

open scoped Classical

noncomputable section

/--
The number of lines in the arrangement passing through a point.
-/
def Arrangement.multiplicity (A : Arrangement) (p : ℝ × ℝ) : ℕ :=
  (A.lines.filter (fun l => l.contains p)).card

/--
A point is ordinary if exactly two lines pass through it.
-/
def Arrangement.IsOrdinaryPoint (A : Arrangement) (p : ℝ × ℝ) : Prop :=
  A.multiplicity p = 2

/--
A set of three lines forms an ordinary triangle if they have three distinct intersection
points and each vertex is an ordinary point of the arrangement.
-/
def Arrangement.IsOrdinaryTriangle (A : Arrangement) (S : Finset Line) : Prop :=
  S ⊆ A.lines ∧ S.card = 3 ∧
  ∃ p1 p2 p3 : ℝ × ℝ, p1 ≠ p2 ∧ p1 ≠ p3 ∧ p2 ≠ p3 ∧
    (∀ p ∈ ({p1, p2, p3} : Set (ℝ × ℝ)), A.IsOrdinaryPoint p) ∧
    (∀ l ∈ S, l.contains p1 ∨ l.contains p2 ∨ l.contains p3) ∧
    (∀ l ∈ S, (l.contains p1 ∧ l.contains p2) ∨ (l.contains p1 ∧ l.contains p3) ∨ (l.contains p2 ∧ l.contains p3))

end

/--
Does every arrangement of $d \ge 4$ non-parallel lines with no 4-concurrent points contain
an ordinary triangle?

Escudero [Es16] disproved this for all $d \ge 4$.

[Es16] Escudero, J. S., _Ordinary triangles in arrangements of lines_,
Discrete & Computational Geometry (2016).
-/
@[category research solved, AMS 52]
theorem erdos_209 : answer(False) ↔ ∀ (d : ℕ), d ≥ 4 →
    ∀ (A : Arrangement), A.lines.card = d →
    (∀ p, A.multiplicity p < 4) →
    ∃ S, A.IsOrdinaryTriangle S := by
  sorry

end Erdos209
