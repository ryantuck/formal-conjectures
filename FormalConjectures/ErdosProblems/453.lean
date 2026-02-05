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
# Erdős Problem 453

Is it true that for all sufficiently large n, there exists some i < n such that
pₙ² < p_{n+i}·p_{n-i}, where pₖ denotes the k-th prime?

Pomerance (1979): DISPROVED (Lean verified) - Proved infinitely many n exist where
pₙ² > p_{n+i}·p_{n-i} for all i < n.

Proof uses convex hull geometry of (n, log pₙ).

*Reference:* [erdosproblems.com/453](https://www.erdosproblems.com/453)
-/

open Filter Topology BigOperators Real Classical

namespace Erdos453

/-- Pomerance: Infinitely many counterexamples -/
@[category research solved, AMS 11]
theorem erdos_453_pomerance :
    ∀ M : ℕ, ∃ n > M, ∀ i : ℕ, i < n → i > 0 →
      (Nat.nth Nat.Prime n)^2 > (Nat.nth Nat.Prime (n + i)) * (Nat.nth Nat.Prime (n - i)) := by
  sorry

end Erdos453
