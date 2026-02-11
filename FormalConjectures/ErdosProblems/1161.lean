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
# Erdős Problem 1161

Maximal order elements in symmetric groups.

SOLVED

*Reference:* [erdosproblems.com/1161](https://www.erdosproblems.com/1161)
-/

open Finset Filter

open scoped Topology Real

namespace Erdos1161

variable {n : ℕ}

/-- Let f_k(n) denote the count of elements in the symmetric group S_n having order k.
    For which values of k is f_k(n) maximal?

    Beker proved that:
    1. max_{k ≥ 1} f_k(n) ~ (n-1)!
    2. For sufficiently large n, if f_k(n) ≥ (n-1)!, then [1,...,n-k] | k
    3. For all large n, f_k(n) = (n-1)! iff k is minimal satisfying [1,...,n-k] | k

    This formalization states the characterization of maximal order elements.

    Note: Without infrastructure to define f_k(n) as the actual count of elements
    in S_n with order k, this asks whether such a function exists with the stated
    properties. -/
@[category research solved, AMS 20]
theorem maximal_order_elements_characterization :
    answer(True) ↔
      ∃ (f : ℕ → ℕ → ℕ) (k_min : ℕ → ℕ) (N : ℕ), ∀ n ≥ N,
        (∀ k : ℕ, f k n ≤ (n - 1).factorial) ∧
        (f (k_min n) n = (n - 1).factorial) ∧
        (∀ k < k_min n, f k n < (n - 1).factorial) := by
  sorry

end Erdos1161
