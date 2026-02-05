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
# Erdős Problem 1000

Let A = {n₁ < n₂ < ...} be an infinite sequence of integers, and let φₐ(k) count
the number of 1 ≤ m ≤ nₖ such that the fraction m/nₖ does not have denominator nⱼ
for j < k when written in lowest form; equivalently, nₖ/gcd(m,nₖ) ≠ nⱼ for all 1 ≤ j < k.

Is there a sequence A such that lim_{N→∞} (1/N)·∑_{k≤N} φₐ(k)/nₖ = 0?

Haight: PROVED - Such a sequence exists (contrary to Erdős' expectations).

*Reference:* [erdosproblems.com/1000](https://www.erdosproblems.com/1000)
-/

open Filter Topology BigOperators Real Classical

namespace Erdos1000

/-- φₐ(k) counts fractions with new denominators -/
noncomputable def phi_A (A : ℕ → ℕ) (k : ℕ) : ℕ :=
  Nat.card {m : ℕ | 1 ≤ m ∧ m ≤ A k ∧ ∀ j < k, (A k) / (Nat.gcd m (A k)) ≠ A j}

/-- Haight: Sequence with vanishing average -/
@[category research solved, AMS 11]
theorem erdos_1000_haight :
    ∃ A : ℕ → ℕ, StrictMono A ∧
      Tendsto (fun N : ℕ =>
        (1 / N : ℝ) * (Finset.range N).sum (fun k => (phi_A A k : ℝ) / (A k)))
        atTop (𝓝 0) := by
  sorry

end Erdos1000