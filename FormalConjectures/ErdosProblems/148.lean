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
# Erdős Problem 148

*Reference:* [erdosproblems.com/148](https://www.erdosproblems.com/148)
-/

namespace Erdos148

open Finset Real Classical

/--
A set of distinct integers `S` is a solution if $\sum_{n \in S} \frac{1}{n} = 1$.
-/
def IsSolution (S : Finset ℕ) : Prop :=
  (∑ n ∈ S, (1 : ℚ) / n) = 1

/--
`SolutionSet k` is the set of all solutions of size `k`.
-/
def SolutionSet (k : ℕ) : Set (Finset ℕ) :=
  { S | S.card = k ∧ IsSolution S }

/--
It is a known fact that the number of solutions is finite for any fixed `k`.
-/
axiom SolutionSet_Finite (k : ℕ) : (SolutionSet k).Finite

/--
`F(k)` is the number of solutions of size `k`.
-/
noncomputable def F (k : ℕ) : ℕ :=
  (SolutionSet_Finite k).toFinset.card

/--
The problem asks for estimates of `F(k)`.
Known bounds exist but the precise asymptotics are open.
-/
@[category research open, AMS 11]
theorem erdos_148 :
    answer(sorry) ↔ True := by
  sorry

end Erdos148
