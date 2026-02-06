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
# Erdős Problem 690

Is the density of integers with k-th smallest prime factor p unimodal in p?

OPEN (Cambie 2025: unimodal for k ≤ 3, not for k ≥ 4)

*Reference:* [erdosproblems.com/690](https://www.erdosproblems.com/690)
-/

open Nat

open scoped Topology Real

namespace Erdos690

/-- d_k(p): density of integers with k-th smallest prime factor p -/
noncomputable def d_k (k : ℕ) (p : ℕ) : ℝ := sorry

/-- Is d_k(p) unimodal in p? -/
@[category research open, AMS 11]
theorem density_kth_prime_factor_unimodal (k : ℕ) (answer : Prop) :
    answer ↔ ∀ p q r : ℕ, p.Prime → q.Prime → r.Prime →
      p < q → q < r →
      d_k k q ≥ min (d_k k p) (d_k k r) := by
  sorry

end Erdos690
