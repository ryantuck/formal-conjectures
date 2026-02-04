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
# Erdős Problem 224

*Reference:* [erdosproblems.com/224](https://www.erdosproblems.com/224)
-/

open EuclideanGeometry

namespace Erdos224

/--
The angle $\angle abc$ is obtuse if it is strictly greater than $\pi/2$.
-/
def IsObtuse {d : ℕ} (a b c : EuclideanSpace ℝ (Fin d)) : Prop :=
  angle a b c > Real.pi / 2

/--
If $A \subseteq \mathbb{R}^d$ is any set of $2^d + 1$ points then some three points
in $A$ determine an obtuse angle.

This was proved by Danzer and Grünbaum [DaGr62].

[DaGr62] Danzer, L. and Grünbaum, B., _Über zwei Probleme bezüglich konvexer Körper von P. Erdős und von V. L. Klee_.
  Math. Z. (1962), 214-230.
-/
@[category research solved, AMS 52]
theorem erdos_224 : ∀ {d : ℕ} (A : Finset (EuclideanSpace ℝ (Fin d))),
    A.card = 2^d + 1 →
    ∃ a b c, a ∈ A ∧ b ∈ A ∧ c ∈ A ∧ a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ IsObtuse a b c := by
  sorry

/--
The number $2^d + 1$ is sharp, as shown by the vertices of a $d$-dimensional cube.
The vertices of a $d$-cube have no obtuse angles.
-/
@[category research solved, AMS 52]
theorem erdos_224.sharp : ∀ d : ℕ,
    ∃ A : Finset (EuclideanSpace ℝ (Fin d)), A.card = 2^d ∧
      ∀ a b c, a ∈ A → b ∈ A → c ∈ A → a ≠ b → b ≠ c → a ≠ c → ¬ IsObtuse a b c := by
  sorry

end Erdos224
