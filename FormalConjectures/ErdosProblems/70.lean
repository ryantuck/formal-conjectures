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
import Mathlib.SetTheory.Ordinal.Exponential

/-! 
# Erdős Problem 70

*Reference:* [erdosproblems.com/70](https://www.erdosproblems.com/70)
-/

namespace Erdos70

open Cardinal Ordinal

/--
A better way to state it: for any 2-coloring of the 3-element subsets of $\alpha$,
there is a subset of type $\beta$ with all its 3-element subsets color 0,
or a subset of size $n$ with all its 3-element subsets color 1.
-/ 
def IsOrdinalRamsey (α β : Ordinal) (n : ℕ) : Prop :=
  ∀ (f : { s : Set α.toType // s.ncard = 3 } → Fin 2),
    (∃ (S : Set α.toType), typeLT S = β ∧ ∀ (s : Set α.toType) (_ : s ⊆ S) (hc : s.ncard = 3),
      f ⟨s, hc⟩ = 0) ∨
    (∃ (S : Set α.toType), S.ncard = n ∧ ∀ (s : Set α.toType) (_ : s ⊆ S) (hc : s.ncard = 3),
      f ⟨s, hc⟩ = 1)

/--
Let $\mathfrak{c}$ be the ordinal of the real numbers, $\beta$ be any countable ordinal,
and $2\leq n<\omega$. Is it true that $\mathfrak{c}\to (\beta, n)_2^3$?
-/ 
@[category research open, AMS 03 05] 
theorem erdos_70 : answer(sorry) ↔ ∀ (β : Ordinal), β.card ≤ aleph 0 → ∀ (n : ℕ), 2 ≤ n →
    IsOrdinalRamsey continuum.ord β n := by
  sorry

end Erdos70