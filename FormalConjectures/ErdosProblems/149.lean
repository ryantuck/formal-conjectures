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
import Mathlib.Combinatorics.SimpleGraph.Coloring

/-!
# Erdős Problem 149

*Reference:* [erdosproblems.com/149](https://www.erdosproblems.com/149)
-/

namespace Erdos149

open SimpleGraph Finset Real Classical Sym2

/--
The maximum degree of the graph G.
-/
def MaxDegree {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  univ.sup (fun v => G.degree v)

/--
The square of a graph G.
-/
def Square {V : Type*} (G : SimpleGraph V) : SimpleGraph V :=
  { Adj := fun u v => u ≠ v ∧ (G.Adj u v ∨ ∃ w, G.Adj u w ∧ G.Adj w v),
    symm := fun u v ⟨hneq, h⟩ => ⟨hneq.symm, by
      rcases h with h | ⟨w, h1, h2⟩
      · left; exact h.symm
      · right; exact ⟨w, h2.symm, h1.symm⟩⟩,
    loopless := fun x ⟨hneq, _⟩ => hneq rfl }

/--
The line graph of G. Vertices are edges of G.
We represent edges as elements of G.edgeFinset (subtype of Sym2 V).
-/
def LineGraph {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    SimpleGraph G.edgeFinset :=
  SimpleGraph.fromRel (fun e1 e2 => e1 ≠ e2 ∧ ∃ v, v ∈ e1.val ∧ v ∈ e2.val)

/--
The conjecture is that the chromatic number of the square of the line graph of G
is at most (5/4) * Δ^2.
-/
@[category research open, AMS 05]
theorem erdos_149 :
    answer(sorry) ↔ ∀ n, ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      ((Square (LineGraph G)).chromaticNumber.toNat : ℝ) ≤ (5 / 4 : ℝ) * (MaxDegree G : ℝ) ^ 2 := by
  sorry

end Erdos149
