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
# Erdős Problem 171

*Reference:* [erdosproblems.com/171](https://www.erdosproblems.com/171)

The Density Hales-Jewett theorem.
-/

namespace Erdos171

/--
A combinatorial line in $[t]^N$ is a set of $t$ points $P = \{p_1, \dots, p_t\}$ such that there
is a non-empty set of coordinates $S \subseteq \{1, \dots, N\}$ and for each $j \in \{1, \dots, N\}$,
the $j$-th coordinate of $p_i$ is $i$ if $j \in S$, and constant otherwise.
-/
def IsCombinatorialLine {t N : ℕ} (L : Finset (Fin N → Fin t)) : Prop :=
  ∃ (S : Finset (Fin N)) (_ : S.Nonempty) (c : Fin N → Fin t),
    L = Finset.univ.image fun (i : Fin t) =>
      fun (j : Fin N) => if j ∈ S then i else c j

/--
For every $\epsilon > 0$ and integer $t \geq 1$, if $N$ is sufficiently large and
$A \subseteq [t]^N$ is of size at least $\epsilon t^N$ then $A$ contains a combinatorial line.
-/
@[category research solved, AMS 5 11]
theorem erdos_171 :
    ∀ (t : ℕ) (_ : t ≥ 1) (ε : ℝ) (_ : ε > 0),
    ∀ᶠ (N : ℕ) in Filter.atTop,
    ∀ (A : Finset (Fin N → Fin t)),
    (A.card : ℝ) ≥ ε * (t : ℝ) ^ N →
    ∃ (L : Finset (Fin N → Fin t)), L ⊆ A ∧ IsCombinatorialLine L := by
  sorry

end Erdos171
