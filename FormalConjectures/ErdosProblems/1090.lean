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
# Erdős Problem 1090

Monochromatic lines in colored finite sets.

PROVED

*Reference:* [erdosproblems.com/1090](https://www.erdosproblems.com/1090)
-/

open Finset

open scoped Topology Real

namespace Erdos1090

/-- A set of points in a Euclidean space is a line if it is an affine subspace of dimension 1. -/
def IsLine {V : Type*} [AddCommGroup V] [Module ℝ V] (L : Set V) : Prop :=
  ∃ (v : V) (w : V), w ≠ 0 ∧ L = {u | ∃ (t : ℝ), u = v + t • w}

/-- English version: Let k ≥ 3. Does there exist a finite set A ⊆ ℝ² such that, in any 2-colouring of A, there exists a line which contains at least k points from A, and all the points of A on the line have the same colour? -/
@[category research solved, AMS 05]
theorem monochromatic_lines (k : ℕ) (hk : 3 ≤ k) :
    answer(True) ↔
    ∃ (A : Finset (EuclideanSpace ℝ (Fin 2))),
      ∀ (f : EuclideanSpace ℝ (Fin 2) → Fin 2),
        ∃ (L : Set (EuclideanSpace ℝ (Fin 2))) (c : Fin 2),
          IsLine L ∧ 
          letI := Classical.propDecidable
          k ≤ (A.filter (λ x => x ∈ L ∧ f x = c)).card := by
  sorry

end Erdos1090
