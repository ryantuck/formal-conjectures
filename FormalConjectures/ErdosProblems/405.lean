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
# Erdős Problem 405

For odd prime $p$, does $(p-1)! + a^{p-1} = p^k$ have only finitely many solutions?

PROVED by Brindza-Erdős (1991): YES, finitely many.
Yu-Liu (1996): Complete list: (2,1,3), (2,5,3^3), (4,1,5^2) as (p-1,a,p^k).

Example: 6! + 2^6 = 28^2.

*Reference:* [erdosproblems.com/405](https://www.erdosproblems.com/405)
-/

open Filter Topology BigOperators

namespace Erdos405

/-- Brindza-Erdős: Only finitely many solutions -/
@[category research solved, AMS 11]
theorem erdos_405_brindza_erdos :
    ∃ B : ℕ, ∀ p a k : ℕ, p.Prime → p % 2 = 1 →
      (p - 1).factorial + a^(p - 1) = p^k → p ≤ B := by
  sorry

/-- Yu-Liu: Complete classification of solutions -/
@[category research solved, AMS 11]
theorem erdos_405_yu_liu :
    ∀ p a k : ℕ, p.Prime → p % 2 = 1 →
      (p - 1).factorial + a^(p - 1) = p^k →
      (p, a, k) = (3, 1, 1) ∨ (p, a, k) = (3, 5, 3) ∨ (p, a, k) = (5, 1, 2) := by
  sorry

end Erdos405
