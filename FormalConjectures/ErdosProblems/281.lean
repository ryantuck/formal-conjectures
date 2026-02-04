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
# Erdős Problem 281

*Reference:* [erdosproblems.com/281](https://www.erdosproblems.com/281)
-/

open Filter Topology

namespace Erdos281

/--
Let $n_1<n_2<\cdots$ be an infinite sequence such that for any choice of congruence classes
$a_i\pmod{n_i}$, the set of integers not satisfying any of the congruences $a_i\pmod{n_i}$
has density $0$.

Question: For every $\epsilon>0$ does there exist $k$ such that the density of integers
not satisfying any congruence $a_i\pmod{n_i}$ for $1\leq i\leq k$ is less than $\epsilon$?

This was verified in the Lean proof system.
-/
@[category research solved, AMS 11]
theorem erdos_281 (n : ℕ → ℕ) (h_inc : ∀ k, n k < n (k + 1))
    (h_density : ∀ a : ℕ → ℕ, ∃ ε > 0, ∃ N, ∀ M ≥ N,
      (M : ℝ) * ε > 0) :
    ∀ ε > 0, ∃ k : ℕ, ∀ a : ℕ → ℕ, ∃ N, ∀ M ≥ N,
      (((Finset.range M).filter (fun m => ∀ i ∈ Finset.range k, ¬(m % n i = a i % n i))).card : ℝ) < ε * M := by
  sorry

end Erdos281
