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
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

/-!
# Erdős Problem 165

*Reference:* [erdosproblems.com/165](https://www.erdosproblems.com/165)

Give an asymptotic formula for $R(3,k)$.
-/

namespace Erdos165

open SimpleGraph Combinatorics Asymptotics Filter Real

/--
The Ramsey number $R(3,k)$ is the smallest $n$ such that every graph on $n$ vertices
contains a triangle or an independent set of size $k$.
-/
noncomputable def erdos_165_Ramsey (k : ℕ) : ℕ :=
  sInf { n | ∀ (G : SimpleGraph (Fin n)), ¬ G.CliqueFree 3 ∨ α(G) ≥ k }

/--
Give an asymptotic formula for $R(3,k)$.

The conjecture is that $R(3,k) \sim \frac{1}{2}\frac{k^2}{\log k}$.

[Ki95] J. H. Kim, "The Ramsey number $R(3,k)$ has order of magnitude $k^2/\log k$",
Random Structures Algorithms 7 (1995), 173–207.
[Sh83] J. B. Shearer, "A note on the independence number of triangle-free graphs",
Discrete Math. 46 (1983), 83–87.
[CJMS25] M. Campos, M. Jenssen, M. Michelen, and S. Sahasrabudhe,
"The lower bound for $R(3,k)$", arXiv:2501.03234 (2025).
[HHKP25] D. Hefty, W. Horn, K. King, and F. Pfender,
"An improved lower bound for $R(3,k)$", arXiv:2504.17644 (2025).
-/
@[category research open, AMS 05]
theorem erdos_165 : answer(sorry) ↔ 
    (fun k ↦ (erdos_165_Ramsey k : ℝ)) ~[atTop] (fun k ↦ k^2 / (2 * log k)) := by
  sorry

end Erdos165
