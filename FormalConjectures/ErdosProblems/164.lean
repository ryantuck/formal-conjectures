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
# Erdős Problem 164

*Reference:* [erdosproblems.com/164](https://www.erdosproblems.com/164)

A set $A \subset \mathbb{N}$ is primitive if no member of $A$ divides another.
Is the sum $\sum_{n \in A} \frac{1}{n \log n}$ maximised over all primitive sets
when $A$ is the set of primes?

Erdős proved that this sum always converges for any primitive set (excluding 1).
Lichtman proved that the answer is yes.
-/

namespace Erdos164

open Filter Real Nat

/--
A set of natural numbers is primitive if no member divides another.
-/
def IsPrimitive (A : Set ℕ) : Prop :=
  ∀ {m n : ℕ}, m ∈ A → n ∈ A → m ∣ n → m = n

/--
The Erdős conjecture (now theorem) that the sum $\sum_{n \in A} \frac{1}{n \log n}$
for a primitive set $A \subseteq \{2, 3, \dots\}$ is maximized when $A$ is the set of primes.
-/
@[category research solved, AMS 11]
theorem erdos_164 :
    ∀ (A : Set ℕ), IsPrimitive A → (∀ n ∈ A, 1 < n) →
    ∑' (n : A), 1 / ((n : ℝ) * Real.log n) ≤ ∑' (p : {p : ℕ | p.Prime}), 1 / ((p : ℝ) * Real.log p) := by
  sorry

end Erdos164
