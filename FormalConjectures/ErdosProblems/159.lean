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
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

/-!
# Erdős Problem 159

*Reference:* [erdosproblems.com/159](https://www.erdosproblems.com/159)
-/

open SimpleGraph Asymptotics Filter

open scoped SimpleGraph

namespace Erdos159

/-- $R(C_4, K_n)$ is the smallest $N$ such that every graph on $N$ vertices contains a $C_4$ 
as a subgraph or an independent set of size $n$. -/
noncomputable def erdos_159_Ramsey (n : ℕ) : ℕ :=
  sInf { N | ∀ (G : SimpleGraph (Fin N)), (cycleGraph 4) ⊑ G ∨ α(G) ≥ n }

/--
There exists some constant $c>0$ such that $R(C_4,K_n) \ll n^{2-c}$.

The current known bounds for $R(C_4,K_n)$ are:
$$ \frac{n^{3/2}}{(\log n)^{3/2}}\ll R(C_4,K_n)\ll \frac{n^2}{(\log n)^2}.$$
The upper bound is due to Szemerédi and the lower bound is due to Spencer [Sp77].

[Sp77] J. Spencer, "Asymptotic lower bounds for Ramsey functions", Discrete Math. 20 (1977), 69–76.
-/
@[category research open, AMS 05]
theorem erdos_159 : answer(sorry) ↔ ∃ c > 0, 
    (fun n : ℕ ↦ (erdos_159_Ramsey n : ℝ)) =O[atTop] (fun n ↦ (n : ℝ) ^ (2 - c)) := by
  sorry

end Erdos159
