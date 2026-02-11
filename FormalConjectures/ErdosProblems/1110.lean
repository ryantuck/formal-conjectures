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
# Erdős Problem 1110

Representability using powers of coprime integers.

OPEN

*Reference:* [erdosproblems.com/1110](https://www.erdosproblems.com/1110)
-/

open Finset

open scoped Real

namespace Erdos1110

/-- A term of the form p^k * q^l -/
def pqTerm (p q : ℕ) : Set ℕ :=
  {n | ∃ k l : ℕ, n = p ^ k * q ^ l}

/-- A number is representable if it is a sum of elements from pqTerm
    such that no summand divides another -/
def Representable (p q : ℕ) (n : ℕ) : Prop :=
  ∃ (S : Finset ℕ), (↑S ⊆ pqTerm p q) ∧
    (∀ a ∈ S, ∀ b ∈ S, a ≠ b → ¬(a ∣ b)) ∧
    S.sum id = n

/-- For coprime p > q >= 2 with {p,q} != {2,3},
    the set of non-representable numbers is infinite -/
@[category research open, AMS 11]
theorem coprime_power_representation (p q : ℕ) (hq : 2 ≤ q) (hp : q < p)
    (hcop : Nat.Coprime p q) (hne : ¬((p = 2 ∧ q = 3) ∨ (p = 3 ∧ q = 2))) :
    {n : ℕ | ¬Representable p q n}.Infinite := by
  sorry

end Erdos1110
