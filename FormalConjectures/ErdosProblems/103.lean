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
import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.MetricSpace.Isometry

/-! 
# Erdős Problem 103

*Reference:* [erdosproblems.com/103](https://www.erdos.com/103)
-/ 

namespace Erdos103

open scoped EuclideanGeometry
open Classical

/--
Let $h(n)$ count the number of incongruent sets of $n$ points in $\mathbb{R}^2$ which minimise
the diameter subject to the constraint that $d(x,y)\geq 1$ for all points $x\neq y$.
Is it true that $h(n)\to \infty$? 
-/ 

def Separated (A : Finset (EuclideanSpace ℝ (Fin 2))) : Prop := 
  ∀ x ∈ A, ∀ y ∈ A, x ≠ y → dist x y ≥ 1

noncomputable def diameter (A : Finset (EuclideanSpace ℝ (Fin 2))) : ℝ := 
  if A.Nonempty then 
    ⨆ (p : A × A), dist p.1 p.2 
  else 0

noncomputable def minDiameter (n : ℕ) : ℝ := 
  sInf { d | ∃ (A : Finset (EuclideanSpace ℝ (Fin 2))), A.card = n ∧ Separated A ∧ diameter A = d }

def IsCongruent (A B : Finset (EuclideanSpace ℝ (Fin 2))) : Prop := 
  ∃ φ : EuclideanSpace ℝ (Fin 2) ≃ᵢ EuclideanSpace ℝ (Fin 2), A.map φ.toEmbedding = B

noncomputable def OptimalSets (n : ℕ) : Set (Finset (EuclideanSpace ℝ (Fin 2))) := 
  { A | A.card = n ∧ Separated A ∧ diameter A = minDiameter n }

-- We define h(n) as the number of equivalence classes of OptimalSets under IsCongruent.
-- Since we can't easily quotient a Set by a Prop-valued relation in a way that gives us a type to count, 
-- we'll define it via the existence of a set of representatives.

noncomputable def h (n : ℕ) : ℕ := 
  Set.ncard { C | ∃ A ∈ OptimalSets n, C = { B | IsCongruent A B } ∩ OptimalSets n }

@[category research open, AMS 52]
theorem erdos_103 : answer(sorry) ↔ Filter.Tendsto (fun n ↦ (h n : ℝ)) Filter.atTop Filter.atTop := by 
  sorry

end Erdos103