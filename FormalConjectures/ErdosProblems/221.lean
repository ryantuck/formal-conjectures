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
# Erdős Problem 221

*Reference:* [erdosproblems.com/221](https://www.erdosproblems.com/221)
-/

open Filter

namespace Erdos221

/--
Every large integer can be written as $2^k + a$ for some $k \ge 0$ and $a \in A$.
-/
def IsAdditiveComplementOfPowersOfTwo (A : Set ℕ) : Prop :=
  ∀ᶠ n : ℕ in atTop, ∃ k : ℕ, ∃ a ∈ A, 2^k + a = n

/--
Is there a set $A \subseteq \mathbb{N}$ such that $|A \cap \{1, \dots, N\}| \ll N/\log N$
and such that every large integer can be written as $2^k + a$ for some $k \ge 0$ and $a \in A$?
-/
@[category research solved, AMS 11]
theorem erdos_221 : ∃ A : Set ℕ,
    (∃ C > 0, ∀ᶠ N : ℕ in atTop, (A ∩ Finset.range (N + 1)).ncard ≤ C * N / Real.log N) ∧
    IsAdditiveComplementOfPowersOfTwo A := by
  sorry

/--
Ruzsa [Ru01] constructed such a set $A$ with $|A \cap \{1, \dots, N\}| \sim N/\log_2 N$.

[Ru01] Ruzsa, I. Z., _On a problem of Erdős concerning the proximity of consecutive elements of an additive basis_.
  Acta Arith. (2001), 329-336.
-/
@[category research solved, AMS 11]
theorem erdos_221.ruzsa_best : ∃ A : Set ℕ,
    Tendsto (fun N ↦ (A ∩ Finset.range (N + 1)).ncard * Real.log 2 / N * Real.log N) atTop (nhds 1) ∧
    IsAdditiveComplementOfPowersOfTwo A := by
  sorry

end Erdos221
