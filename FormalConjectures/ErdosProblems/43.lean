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
import FormalConjecturesForMathlib.Combinatorics.Basic

/-!
# Erdős Problem 43

*Reference:* [erdosproblems.com/43](https://www.erdosproblems.com/43)
-/

namespace Erdos43

open scoped BigOperators Pointwise

/--
The maximum size of a Sidon set in `{1, ..., N}`.
-/
noncomputable def f (N : ℕ) : ℕ :=
  sSup {((A.ncard) : ℕ) | (A : Set ℕ) (_ : A ⊆ Finset.Icc 1 N) (_ : IsSidon A)}

/--
If `A, B` are Sidon sets in `{1, ..., N}` such that `(A - A) ∩ (B - B) = {0}`, then is it true that
$\binom{|A|}{2} + \binom{|B|}{2} \le \binom{f(N)}{2} + O(1)$?

If $|A| = |B|$, can this bound be improved to $(1-c)\binom{f(N)}{2}$?
Barreto (in comments) gave a negative answer to the second question.
The first question is open.
-/
@[category research open, AMS 11]
theorem erdos_43 : answer(sorry) ↔ ∃ C : ℝ, ∀ N : ℕ, ∀ A B : Set ℕ,
    A ⊆ Finset.Icc 1 N → B ⊆ Finset.Icc 1 N →
    IsSidon A → IsSidon B →
    let Az : Set ℤ := (Int.ofNat : ℕ → ℤ) '' A
    let Bz : Set ℤ := (Int.ofNat : ℕ → ℤ) '' B
    ((Az - Az) ∩ (Bz - Bz) ⊆ {0}) →
    (Nat.choose A.ncard 2 : ℝ) + (Nat.choose B.ncard 2 : ℝ) ≤ (Nat.choose (f N) 2 : ℝ) + C := by
  sorry

end Erdos43