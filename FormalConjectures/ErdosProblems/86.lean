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
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Erdős Problem 86

*Reference:* [erdosproblems.com/86](https://www.erdos.com/86)
-/

namespace Erdos86

open SimpleGraph

/--
Let $Q_n$ be the $n$-dimensional hypercube graph (so that $Q_n$ has $2^n$ vertices and $n2^{n-1}$
edges). Is it true that every subgraph of $Q_n$ with
$$\geq \left(\frac{1}{2}+o(1)\right)n2^{n-1}$$ 
many edges contains a $C_4$?
-/ 
def HypercubeGraph (n : ℕ) : SimpleGraph (Fin n → Bool) :=
  SimpleGraph.fromRel (fun u v ↦ (Finset.univ.filter (fun i ↦ u i ≠ v i)).card = 1)

@[category research open, AMS 05]
theorem erdos_86 : answer(sorry) ↔ ∀ (ε : ℝ), 0 < ε → ∃ (N₀ : ℕ), ∀ (n : ℕ), N₀ ≤ n →
    let Qn := HypercubeGraph n
    ∀ (G : SimpleGraph (Fin n → Bool)), G ≤ Qn →
    (Nat.card G.edgeSet : ℝ) ≥ (1 / 2 + ε) * (n * 2 ^ (n - 1) : ℝ) →
    ∃ (f : cycleGraph 4 ↪g G), True := by
  sorry

end Erdos86
