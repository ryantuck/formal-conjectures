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
# Erdős Problem 570

*Reference:* [erdosproblems.com/570](https://www.erdosproblems.com/570)

## Statement (PROVED)
Let k ≥ 3. For any graph H on m edges without isolated vertices (with m sufficiently large):
R(C_k,H) ≤ 2m + ⌊(k-1)/2⌋

Proved for even k by Erdős, Faudree, Rousseau, and Schelp.
Proved for k=3 by Goddard & Kleitman and Sidorenko.
Proved for k=5 by Jayawardene.
Proved for all odd k ≥ 7 by Cambie, Freschi, Morawski, Petrova, and Pokrovskiy.

## Source
[EFRS93], Question 5
-/

open SimpleGraph

open scoped Topology Real

namespace Erdos570

variable {α β : Type*}

/-- Ramsey number R(G,H) -/
def ramseyNumber (G : SimpleGraph α) (H : SimpleGraph β) : ℕ := sorry

/-- The cycle graph on n vertices -/
def cycleGraph (n : ℕ) : SimpleGraph (Fin n) := sorry

/-- Main theorem: R(C_k,H) ≤ 2m + ⌊(k-1)/2⌋ for sufficiently large m (PROVED) -/
@[category research solved, AMS 05]
theorem ramsey_cycle_bound (k : ℕ) (hk : k ≥ 3) :
    ∃ M : ℕ, ∀ (H : SimpleGraph β) (m : ℕ),
      H.edgeSet.ncard = m →
      m ≥ M →
      (∀ v, ∃ w, H.Adj v w) →
      ramseyNumber (cycleGraph k) H ≤ 2 * m + (k - 1) / 2 :=
  sorry

end Erdos570
