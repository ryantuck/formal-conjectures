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
# Erdős Problem 384

If $1 < k < n-1$ then $\binom{n}{k}$ is divisible by a prime $p < n/2$
(except $\binom{7}{3} = 5 \cdot 7$).

PROVED by Ecklund (Erdős-Selfridge conjecture).

Ecklund's stronger conjecture: When $n > k^2$, $\binom{n}{k}$ is divisible by a prime $p < n/k$.

*Reference:* [erdosproblems.com/384](https://www.erdosproblems.com/384)
-/

open Filter Topology BigOperators

namespace Erdos384

/-- Ecklund: Binomial coefficient has prime factor < n/2 -/
@[category research solved, AMS 11]
theorem erdos_384_ecklund :
    ∀ n k : ℕ, 1 < k → k < n - 1 → (n, k) ≠ (7, 3) →
      ∃ p : ℕ, p.Prime ∧ p < n / 2 ∧ p ∣ Nat.choose n k := by
  sorry

/-- Ecklund's stronger conjecture: prime factor < n/k when n > k² -/
@[category research open, AMS 11]
theorem erdos_384_ecklund_stronger :
    ∀ n k : ℕ, n > k^2 →
      ∃ p : ℕ, p.Prime ∧ p < n / k ∧ p ∣ Nat.choose n k := by
  sorry

end Erdos384
