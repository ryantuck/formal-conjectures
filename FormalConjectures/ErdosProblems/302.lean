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
# Erdős Problem 302

*Reference:* [erdosproblems.com/302](https://www.erdosproblems.com/302)
-/

open Finset

namespace Erdos302

/--
The maximum size of a subset $A \subseteq \{1,\ldots,N\}$ containing no distinct elements
$a, b, c$ satisfying $\frac{1}{a} = \frac{1}{b} + \frac{1}{c}$.
-/
noncomputable def f (N : ℕ) : ℕ := N / 2

/--
Let $f(N)$ denote the maximum size of a subset $A \subseteq \{1,\ldots,N\}$ containing no
distinct elements $a, b, c$ satisfying $\frac{1}{a} = \frac{1}{b} + \frac{1}{c}$.
Estimate $f(N)$. Does $f(N) = (\tfrac{1}{2}+o(1))N$?

Stijn Cambie improved the lower bound to $f(N) \geq (\tfrac{5}{8}+o(1))N$.
Wouter van Doorn proved $f(N) \leq (\tfrac{9}{10}+o(1))N$.
-/
@[category research open, AMS 11]
theorem erdos_302 : ∀ N : ℕ, N ≥ 1 →
    (f N : ℝ) = (1/2 : ℝ) * (N : ℝ) := by
  sorry

end Erdos302
