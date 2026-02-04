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
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# Erdős Problem 181

*Reference:* [erdosproblems.com/181](https://www.erdosproblems.com/181)

Let $Q_n$ be the $n$-dimensional hypercube graph (so that $Q_n$ has $2^n$ vertices and $n2^{n-1}$
edges). Prove that $R(Q_n) \ll 2^n$.
-/

namespace Erdos181

open SimpleGraph Finset Real Classical

/--
The n-dimensional hypercube graph Qn has vertices as bitstrings of length n,
and edges between bitstrings differing in exactly one position.
-/
def HypercubeGraph (n : ℕ) : SimpleGraph (Fin n → Bool) :=
  SimpleGraph.fromRel (fun u v ↦ (univ.filter (fun i ↦ u i ≠ v i)).card = 1)

/--
The Ramsey number R(H) is the smallest N such that any 2-coloring of the edges of KN
contains a monochromatic copy of H.
-/
noncomputable def graphRamsey {V : Type*} [Fintype V] (H : SimpleGraph V) : ℕ :=
  sInf { N | ∀ (c : Sym2 (Fin N) → Fin 2),
    ∃ (f : V ↪ Fin N) (i : Fin 2), ∀ u v, H.Adj u v → c s(f u, f v) = i }

/--
Erdős and Burr conjectured that R(Qn) = O(2^n).
-/
@[category research open, AMS 05]
theorem erdos_181 :
    ∃ C > 0, ∀ n, (graphRamsey (HypercubeGraph n) : ℝ) ≤ C * 2 ^ n := by
  sorry

end Erdos181
