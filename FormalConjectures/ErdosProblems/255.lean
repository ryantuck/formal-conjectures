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
# Erdős Problem 255

*Reference:* [erdosproblems.com/255](https://www.erdosproblems.com/255)
-/

open Filter Topology MeasureTheory

namespace Erdos255

/--
The discrepancy of a sequence with respect to an interval.
-/
noncomputable def discrepancy (z : ℕ → ℝ) (I : Set ℝ) [∀ n, Decidable (z n ∈ I)] (N : ℕ) : ℝ :=
  ((Finset.range N).filter (fun n => z n ∈ I)).card - (N : ℝ) * (volume I).toReal

/--
Let $z_1,z_2,\ldots \in [0,1]$ be an infinite sequence, and define the discrepancy
$D_N(I) = \#\{ n\leq N : z_n\in I\} - N\lvert I\rvert$.
Must there exist some interval $I\subseteq [0,1]$ such that
$\limsup_{N\to \infty}|D_N(I)| =\infty$?

The answer is yes, as proved by Schmidt [Sc68], who later showed [Sc72] that
this is true for all but countably many intervals of the shape $[0,x]$.

[Sc68] Schmidt, W. M., _Irregularities of distribution III_.
  Pacific J. Math. (1968), 377-385.

[Sc72] Schmidt, W. M., _Irregularities of distribution IV_.
  Invent. Math. (1972), 55-82.
-/
@[category research solved, AMS 11]
theorem erdos_255 : ∀ z : ℕ → ℝ,
    (∀ n, z n ∈ Set.Icc 0 1) →
    ∃ I : Set ℝ, ∃ _inst : ∀ n, Decidable (z n ∈ I),
    I ⊆ Set.Icc 0 1 ∧ MeasurableSet I ∧
    ¬ BddAbove (Set.range (fun N => |discrepancy z I N|)) := by
  sorry

/--
Schmidt proved this for all but countably many intervals of the shape $[0,x]$.
-/
@[category research solved, AMS 11]
theorem erdos_255.schmidt : ∀ z : ℕ → ℝ,
    (∀ n, z n ∈ Set.Icc 0 1) →
    ∀ _inst : ∀ x n, Decidable (z n ∈ Set.Icc 0 x),
    Set.Countable {x : ℝ | x ∈ Set.Icc 0 1 ∧
      BddAbove (Set.range (fun N => |discrepancy z (Set.Icc 0 x) N|))} := by
  sorry

end Erdos255
