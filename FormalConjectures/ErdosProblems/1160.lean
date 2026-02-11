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
# Erdős Problem 1160

Conjecture on the number of groups of a given order.

OPEN

*Reference:* [erdosproblems.com/1160](https://www.erdosproblems.com/1160)
-/

open Finset Filter

open scoped Topology Real

namespace Erdos1160

/-- Let g(n) denote the number of groups (up to isomorphism) of order n.
    Conjecture: If n ≤ 2^m then g(n) ≤ g(2^m).

    Pantelidakis proved this holds when n is odd and m ≥ 3619.

    A stronger variant conjectures that for sufficiently large m,
    ∑_{n < 2^m} g(n) ≤ g(2^m). -/
@[category research open, AMS 20]
theorem group_order_conjecture :
    ∀ (n m : ℕ), n ≤ 2^m →
    ∃ (g : ℕ → ℕ), g n ≤ g (2^m) := by
  sorry

/-- Stronger variant: For sufficiently large m, the sum of g(n) for n < 2^m
    is bounded by g(2^m). -/
@[category research open, AMS 20]
theorem group_order_sum_conjecture :
    ∃ (M : ℕ), ∀ m ≥ M,
      ∃ (g : ℕ → ℕ), (Finset.range (2^m)).sum g ≤ g (2^m) := by
  sorry

end Erdos1160
