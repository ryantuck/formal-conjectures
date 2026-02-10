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
# Erdős Problem 854

Primorial coprime gaps.

OPEN

*Reference:* [erdosproblems.com/854](https://www.erdosproblems.com/854)
-/

open Finset Nat Filter

open scoped Topology Real

namespace Erdos854

/-- The k-th primorial: product of the first k primes -/
noncomputable def primorial (k : ℕ) : ℕ :=
  (Finset.range k).prod (fun i => Nat.nth Nat.Prime (i + 1))

/-- The sequence of integers in [1, n_k-1] coprime to n_k -/
noncomputable def coprimeSeq (k : ℕ) : List ℕ :=
  (List.range (primorial k)).filter (fun n => n > 0 ∧ n < primorial k ∧ Nat.Coprime n (primorial k))

/-- Gaps between consecutive coprime integers -/
def gaps (k : ℕ) : Set ℕ :=
  {d | ∃ (s : List ℕ) (i : ℕ) (hi : i + 1 < s.length),
    s = coprimeSeq k ∧ d = s.get ⟨i + 1, hi⟩ - s.get ⟨i, Nat.lt_trans (Nat.lt_succ_self i) hi⟩}

/-- Question 1: Estimate the smallest even integer not expressible as a gap.
    This is an open estimation problem. -/
@[category research open, AMS 11]
theorem smallest_non_gap_even (k : ℕ) :
    ∃ m : ℕ, Even m ∧ m ∉ gaps k ∧
      ∀ n < m, Even n → n ∈ gaps k := by
  sorry

/-- Question 2: Are there substantially more than max_gap many even integers
    expressible as gaps? -/
@[category research open, AMS 11]
theorem many_even_gaps :
    ∀ᶠ k in atTop, (gaps k ∩ {n | Even n}).ncard > sSup (gaps k) := by
  sorry

end Erdos854
