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
# Erdős Problem 435

Let n ∈ ℕ with n ≠ p^k for any prime p and k ≥ 0. Find the largest integer not
expressible as:
  ∑_{1 ≤ i < n} cᵢ·C(n,i)
where all cᵢ ≥ 0 are integers.

Hwang-Song: PROVED - If n = ∏ pₖ^aₖ, the answer is
  ∑ₖ (∑_{1 ≤ d ≤ aₖ} C(n, pₖ^d))(pₖ - 1) - n

*Reference:* [erdosproblems.com/435](https://www.erdosproblems.com/435)
-/

open Filter Topology BigOperators

namespace Erdos435

/-- Hwang-Song: Largest integer not expressible as binomial sum -/
@[category research solved, AMS 11]
theorem erdos_435_hwang_song :
    ∀ n : ℕ, n > 1 → (∀ p k : ℕ, p.Prime → n ≠ p ^ k) →
      ∃ M : ℕ, (∀ m > M, ∃ c : ℕ → ℕ, m = (Finset.range n).sum (fun i => c i * Nat.choose n i)) ∧
        ¬∃ c : ℕ → ℕ, M = (Finset.range n).sum (fun i => c i * Nat.choose n i) ∧
        M = (n.primeFactors.sum fun p =>
          (Finset.range (n.factorization p + 1)).sum (fun d =>
            if d > 0 then Nat.choose n (p ^ d) * (p - 1) else 0)) - n := by
  sorry

end Erdos435
