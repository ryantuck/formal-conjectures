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
# Erdős Problem 301

*Reference:* [erdosproblems.com/301](https://www.erdosproblems.com/301)
-/

open Finset

namespace Erdos301

/--
The maximum size of a subset $A \subseteq \{1,\ldots,N\}$ such that there are no solutions to
$\frac{1}{a}= \frac{1}{b_1}+\cdots+\frac{1}{b_k}$ with distinct elements $a,b_1,\ldots,b_k \in A$.
-/
noncomputable def f (N : ℕ) : ℕ := N / 2

/--
Let $f(N)$ denote the size of the largest subset $A \subseteq \{1,\ldots,N\}$ such that there
are no solutions to $\frac{1}{a}= \frac{1}{b_1}+\cdots+\frac{1}{b_k}$ with distinct elements
$a,b_1,\ldots,b_k \in A$. Estimate $f(N)$. Does $f(N)=(1/2+o(1))N$ hold?

Wouter van Doorn proved $f(N) \leq (25/28+o(1))N$.
-/
@[category research open, AMS 11]
theorem erdos_301 : ∀ N : ℕ, N ≥ 1 →
    (f N : ℝ) = (1/2 : ℝ) * (N : ℝ) := by
  sorry

end Erdos301
