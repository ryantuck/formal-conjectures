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
# Erdős Problem 246

*Reference:* [erdosproblems.com/246](https://www.erdosproblems.com/246)
-/

namespace Erdos246

/--
The set $\{a^kb^l: k,l\geq 0\}$ where $(a,b)=1$.
-/
def PowerSet (a b : ℕ) : Set ℕ :=
  {n | ∃ k l : ℕ, n = a^k * b^l}

/--
A set is complete if every sufficiently large integer is the sum of distinct elements from the set.
-/
def IsComplete (S : Set ℕ) : Prop :=
  ∃ N₀ : ℕ, ∀ n ≥ N₀, ∃ T : Finset ℕ, (∀ x ∈ T, x ∈ S) ∧ T.sum id = n

/--
Let $(a,b)=1$. The set $\{a^kb^l: k,l\geq 0\}$ is complete - that is, every large integer
is the sum of distinct integers of the form $a^kb^l$ with $k,l\geq 0$.

Proved by Birch [Bi59]. This also follows from a more general result of Cassels [Ca60].

[Bi59] Birch, B. J., _A problem of Erdős and Fuchs concerning sequences of integers_.
  J. London Math. Soc. (1959), 193-196.

[Ca60] Cassels, J. W. S., _Über Basen der natürlichen Zahlenreihe_.
  Abh. Math. Sem. Univ. Hamburg (1960), 221-231.
-/
@[category research solved, AMS 11]
theorem erdos_246 : ∀ a b : ℕ, a > 0 → b > 0 → Nat.Coprime a b →
    IsComplete (PowerSet a b) := by
  sorry

end Erdos246
