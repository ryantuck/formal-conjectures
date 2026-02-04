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
# Erdős Problem 280

*Reference:* [erdosproblems.com/280](https://www.erdosproblems.com/280)
-/

open Filter Topology

namespace Erdos280

/--
Let $n_1 < n_2 < \cdots$ be an infinite sequence of integers with associated $a_k \pmod{n_k}$,
such that for some $\epsilon > 0$ we have $n_k > (1+\epsilon)k\log k$ for all $k$.

Erdős conjectured that:
$$\#\{ m < n_k : m \not\equiv a_i \pmod{n_i} \text{ for } 1 \leq i \leq k \} \neq o(k)$$

This was disproved by the counterexample $n_k = 2^k$ and $a_k = 2^{k-1} + 1$,
which yields only $m=1$ uncovered.
-/
@[category research solved, AMS 11]
theorem erdos_280 : ¬ ∀ ε > 0, ∀ n : ℕ → ℕ, ∀ a : ℕ → ℕ,
    (∀ k, n k < n (k + 1)) →
    (∀ k, (n k : ℝ) > (1 + ε) * (k : ℝ) * Real.log (k : ℝ)) →
    ∀ c > 0, ∃ K, ∀ k ≥ K,
      ((Finset.range (n k)).filter (fun m =>
        ∀ i ∈ Finset.range k, ¬(m % n i = a i % n i))).card ≥ c * (k : ℝ) := by
  sorry

/--
Counterexample: $n_k = 2^k$ and $a_k = 2^{k-1} + 1$ yields only $m=1$ uncovered.
-/
@[category research solved, AMS 11]
theorem erdos_280.counterexample (k : ℕ) (hk : k ≥ 1) :
    let n := fun k : ℕ => 2^k
    let a := fun k : ℕ => 2^(k - 1) + 1
    ((Finset.range (n k)).filter (fun m =>
      ∀ i ∈ Finset.range k, ¬(m % n i = a i % n i))).card = 1 := by
  sorry

end Erdos280
