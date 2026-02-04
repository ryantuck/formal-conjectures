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
# Erdős Problem 178

*Reference:* [erdosproblems.com/178](https://www.erdosproblems.com/178)

Let $A_1, A_2, \dots$ be an infinite collection of infinite sets of integers, say
$A_i = \{a_{i1} < a_{i2} < \dots\}$. Does there exist some $f: \mathbb{N} 	o \{-1, 1\}$ such that
$$ \max_{m, 1 \leq i \leq d} \left\lvert \sum_{1 \leq j \leq m} f(a_{ij}) ightvert \ll_d 1 $$
for all $d \geq 1$?
-/

namespace Erdos178

open Finset

/--
Given an infinite collection of infinite sets $A_i \subseteq \mathbb{N}$,
there exists a $\{-1, 1\}$-colouring of $\mathbb{N}$ such that all prefix sums of
the coloured sets are bounded for each $i$.
-/
@[category research solved, AMS 05 11]
theorem erdos_178 :
    ∀ (A : ℕ → ℕ → ℕ), (∀ i, StrictMono (A i)) →
    ∃ (f : ℕ → ℤ), (∀ n, f n = 1 ∨ f n = -1) ∧
    ∀ (d : ℕ), ∃ (C : ℝ), ∀ (i : ℕ), i < d → ∀ (m : ℕ),
    |∑ j ∈ range m, f (A i j)| ≤ C := by
  sorry

end Erdos178
