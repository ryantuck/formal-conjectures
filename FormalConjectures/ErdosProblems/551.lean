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
# Erdős Problem 551

Prove R(C_k, K_n) = (k-1)(n-1) + 1 for k ≥ n ≥ 3 (except k = n = 3).

DECIDABLE (verified for sufficiently large k in terms of n)

*Reference:* [erdosproblems.com/551](https://www.erdosproblems.com/551)
-/

namespace Erdos551

/-- Ramsey number for cycles and complete graphs -/
@[category research solved, AMS 05]
theorem ramsey_cycle_complete :
    ∀ᶠ (k : ℕ) in Filter.atTop, ∀ (n : ℕ), 3 ≤ n → n ≤ k → ¬(k = 3 ∧ n = 3) →
      sorry := by
  sorry

end Erdos551
