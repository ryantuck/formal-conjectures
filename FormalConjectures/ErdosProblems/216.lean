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
# Erdős Problem 216

*Reference:* [erdosproblems.com/216](https://www.erdosproblems.com/216)
-/

open EuclideanGeometry

namespace Erdos216

/--
The set `P` contains an empty convex `n`-gon.
-/
def HasEmptyConvexNGon (n : ℕ) (P : Finset ℝ²) : Prop :=
  ∃ S : Finset ℝ², S.card = n ∧ S ⊆ P ∧ ConvexIndep S ∧
    ∀ p ∈ P, p ∈ convexHull ℝ (S : Set ℝ²) → p ∈ S

/--
The set of $N$ such that any $N$ points in the plane, no three on a line,
contain an empty convex $k$-gon.
-/
def cardSet (k : ℕ) := { N | ∀ (pts : Finset ℝ²), pts.card = N → NonTrilinear pts.toSet →
  HasEmptyConvexNGon k pts }

/--
Let $g(k)$ be the smallest integer (if any such exists) such that any $g(k)$ points
in $\mathbb{R}^2$ contains an empty convex $k$-gon.
-/
noncomputable def g (k : ℕ) : ℕ :=
  sInf (cardSet k)

/--
Does $g(k)$ exist for all $k$?

This has been solved in the negative: $g(k)$ exists for $k \le 6$ but not for $k \ge 7$.
-/
@[category research solved, AMS 52]
theorem erdos_216 : ¬ ∀ k, (cardSet k).Nonempty := by
  sorry

/--
Erdős observed $g(4) = 5$.
-/
@[category research solved, AMS 52]
theorem erdos_216.g4 : g 4 = 5 := by
  sorry

/--
Harborth [Ha78] showed $g(5) = 10$.

[Ha78] Harborth, H., _Konvexe Fünfecke in ebenen Punktmengen_.
  Elem. Math. (1978), 116-118.
-/
@[category research solved, AMS 52]
theorem erdos_216.g5 : g 5 = 10 := by
  sorry

/--
Nicolás [Ni07] and Gerken [Ge08] independently showed that $g(6)$ exists.

[Ni07] Nicolás, C. M., _The empty hexagon theorem_.
  Discrete Comput. Geom. (2007), 389-397.

[Ge08] Gerken, T., _Empty convex hexagons in planar point sets_.
  Discrete Comput. Geom. (2008), 239-272.
-/
@[category research solved, AMS 52]
theorem erdos_216.g6_exists : (cardSet 6).Nonempty := by
  sorry

/--
Heule and Scheucher [HeSc24] proved $g(6) = 30$.

[HeSc24] Heule, M. J. and Scheucher, M., _The empty hexagon number is 30_.
  arXiv preprint arXiv:2404.16223 (2024).
-/
@[category research solved, AMS 52]
theorem erdos_216.g6 : g 6 = 30 := by
  sorry

/--
Horton [Ho83] showed that $g(k)$ does not exist for $k \ge 7$.

[Ho83] Horton, J. D., _Sets with no empty convex 7-gons_.
  Canad. Math. Bull. (1983), 482-484.
-/
@[category research solved, AMS 52]
theorem erdos_216.not_exists_ge_7 : ∀ k ≥ 7, cardSet k = ∅ := by
  sorry

end Erdos216
