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
# Erdős Problem 21

*Reference:* [erdosproblems.com/21](https://www.erdosproblems.com/21)
-/

namespace Erdos21

open Finset

/--
A family `F` of sets of size `n` is valid if it is intersecting and every set of size `≤ n - 1`
is disjoint from some member of `F`.
-/
def IsValidFamily (n : ℕ) (F : Finset (Finset ℕ)) : Prop :=
  (∀ A ∈ F, A.card = n) ∧
  (∀ A ∈ F, ∀ B ∈ F, (A ∩ B).Nonempty) ∧
  (∀ S : Finset ℕ, S.card ≤ n - 1 → ∃ A ∈ F, Disjoint A S)

/--
`f(n)` is the minimal size of a valid family.
-/
noncomputable def f (n : ℕ) : ℕ :=
  sInf {k | ∃ F, IsValidFamily n F ∧ k = F.card}

/--
Is it true that $f(n) \ll n$?

Solved by Kahn [Ka94] who proved $f(n) \ll n$.

[Ka94] J. Kahn, _On a problem of Erdős and Lovász. II: $n(r)=O(r)$_, J. Amer. Math. Soc. 7 (1994), 125-143.
-/
@[category research solved, AMS 05]
theorem erdos_21 : answer(True) ↔ ∃ C : ℝ, ∀ n : ℕ, n > 0 → (f n : ℝ) ≤ C * n := by
  sorry

end Erdos21
