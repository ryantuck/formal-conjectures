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
# Erdős Problem 535

For r ≥ 3, let f_r(N) denote the maximum size of a subset of {1,...,N} such that
no r-element subset has all pairwise gcds equal. Estimate f_r(N).

Known: f_3(N) ≤ N^(1/2+o(1)) by Abbott-Hanson. Erdős conjectured f_3(N) ≤ N^(c/log log N).

OPEN

*Reference:* [erdosproblems.com/535](https://www.erdosproblems.com/535)
-/

open Nat Finset

namespace Erdos535

/-- Maximum subset with no r-subset having all pairwise gcds equal -/
noncomputable def f (r N : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ (A : Finset ℕ),
    (∀ n ∈ A, 0 < n ∧ n ≤ N) ∧ A.card = k ∧
    ∀ (S : Finset ℕ), S ⊆ A → S.card = r →
      ∃ a b c d, a ∈ S ∧ b ∈ S ∧ c ∈ S ∧ d ∈ S ∧ (a, b) ≠ (c, d) ∧
        Nat.gcd a b ≠ Nat.gcd c d}

/-- Upper bound for f_3(N) -/
@[category research open, AMS 11]
theorem f_3_upper_bound :
    ∃ ε : ℝ, ε > 0 ∧ ∀ᶠ N in Filter.atTop, (f 3 N : ℝ) ≤ (N : ℝ) ^ (1/2 + ε) := by
  sorry

/-- Erdős conjecture: f_3(N) superpolynomial lower bound -/
@[category research open, AMS 11]
theorem f_3_conjecture :
    answer(sorry) ↔ ∃ c : ℝ, c > 0 ∧ ∀ᶠ N in Filter.atTop,
      (f 3 N : ℝ) > N ^ (c / Real.log (Real.log N)) := by
  sorry

end Erdos535
