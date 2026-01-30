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
# Erdős Problem 13

*Reference:* [erdosproblems.com/13](https://www.erdosproblems.com/13)
-/

namespace Erdos13

/--
A set $A \subseteq \{1, \dots, N\}$ is Erdős-Sárközy if there are no $a, b, c \in A$ such that
$a \mid (b + c)$ and $a < \min(b, c)$.
-/
def IsErdosSarkozy (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, a ∣ (b + c) → a ≥ min b c

/--
If $A \subseteq \{1, \dots, N\}$ is such that there are no $a, b, c \in A$ such that $a \mid (b + c)$
and $a < \min(b, c)$, then $|A| \leq N/3 + O(1)$.

The answer is yes, as proved by Bedert [Be23].

[Be23] B. Bedert, _On a problem of Erdős and Sárközy_. arXiv:2301.07000 (2023).
-/
@[category research solved, AMS 11]
theorem erdos_13 : answer(True) ↔ ∃ C : ℝ, ∀ N : ℕ, ∀ A : Finset ℕ,
    (∀ a ∈ A, a ∈ Finset.Icc 1 N) → IsErdosSarkozy A →
    (A.card : ℝ) ≤ (N : ℝ) / 3 + C := by
  sorry

end Erdos13
