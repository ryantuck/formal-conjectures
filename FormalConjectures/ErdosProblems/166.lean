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
# Erdős Problem 166

*Reference:* [erdosproblems.com/166](https://www.erdosproblems.com/166)

Prove that
$$R(4,k) \gg \frac{k^3}{(\log k)^{O(1)}}.$$
-/

namespace Erdos166

open SimpleGraph Combinatorics Asymptotics Filter Real

/--
The Ramsey number $R(4,k)$ is the smallest $n$ such that every graph on $n$ vertices
contains a $K_4$ or an independent set of size $k$.
-/
noncomputable def erdos_166_Ramsey (k : ℕ) : ℕ :=
  sInf { n | ∀ (G : SimpleGraph (Fin n)), ¬ G.CliqueFree 4 ∨ α(G) ≥ k }

/--
Prove that $R(4,k) \gg \frac{k^3}{(\log k)^{O(1)}}$.

Mattheus and Verstraete [MaVe23] proved that $R(4,k) \gg \frac{k^3}{(\log k)^4}$.

[MaVe23] S. Mattheus and J. Verstraete, "The asymptotics of Ramsey numbers $R(4,k)$",
Ann. of Math. (2) 199 (2024), 987–1004.
-/
@[category research solved, AMS 05]
theorem erdos_166 : answer(True) ↔ ∃ C > 0,
    (fun k : ℕ ↦ ((k : ℝ)^3 / (log k)^C : ℝ)) =O[atTop] (fun k ↦ (erdos_166_Ramsey k : ℝ)) := by
  sorry

end Erdos166
