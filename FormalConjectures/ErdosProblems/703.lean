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
# Erdős Problem 703

Estimate T(n,r) - max family size where no A,B have |A∩B|=r.

PROVED by Frankl and Rödl (1987); optimal bounds by Frankl and Füredi ($250 reward)

*Reference:* [erdosproblems.com/703](https://www.erdosproblems.com/703)
-/

open Finset Nat Filter Asymptotics

open scoped Topology Real

namespace Erdos703

variable {α : Type*} [DecidableEq α]

/-- A family of sets has no intersection of size exactly r -/
def NoIntersectionSizeR (𝓕 : Finset (Finset α)) (r : ℕ) : Prop :=
  ∀ A B, A ∈ 𝓕 → B ∈ 𝓕 → A ≠ B → (A ∩ B).card ≠ r

/-- T(n,r): max size of family of subsets of [n] with no intersection of size exactly r -/
noncomputable def T (n r : ℕ) : ℕ :=
  sSup {k | ∃ 𝓕 : Finset (Finset (Fin n)), 𝓕.card = k ∧ NoIntersectionSizeR 𝓕 r}

/-- The trivial case: T(n,0) = 2^(n-1) -/
@[category research solved, AMS 5]
theorem T_zero (n : ℕ) (hn : 0 < n) : T n 0 = 2^(n-1) := by
  sorry

/-- Frankl-Rödl (1987): Exponential bound for T(n,r) in the middle range.
    For every ε > 0, there exists δ > 0 such that T(n,r) < (2-δ)^n
    when εn < r < (1/2 - ε)n. -/
@[category research solved, AMS 5]
theorem frankl_rodl_exponential_bound :
    ∀ ε > 0, ∃ δ > 0, ∀ n r : ℕ,
      (ε * n < r) → (r < (1/2 - ε) * n) →
      (T n r : ℝ) < (2 - δ) ^ n := by
  sorry

end Erdos703
