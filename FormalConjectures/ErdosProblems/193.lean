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
import Mathlib.Geometry.Euclidean.Basic
import Mathlib.Algebra.Group.Pi.Basic
import FormalConjectures.Util.ProblemImports

open BigOperators

namespace Erdos193

open Set

/--
Let $S\subseteq \mathbb{Z}^3$ be a finite set and let $A=\{a_1,a_2,\ldots,\}\subset \mathbb{Z}^3$ be an infinite $S$-walk, so that $a_{i+1}-a_i\in S$ for all $i$. Must $A$ contain three collinear points?
-/
@[category research open, AMS 05 51]
theorem erdos_problem_193 :
    ∀ (S : Set (Fin 3 → ℤ)), S.Finite →
    ∀ (A : ℕ → (Fin 3 → ℤ)), (∀ n, A (n + 1) - A n ∈ S) →
    ∃ i j k, i < j ∧ j < k ∧ Collinear ℝ ({ (fun m => (A i m : ℝ)), (fun m => (A j m : ℝ)), (fun m => (A k m : ℝ)) } : Set (Fin 3 → ℝ)) :=
  sorry

end Erdos193