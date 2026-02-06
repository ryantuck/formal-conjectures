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
# Erdős Problem 667

For fixed integers p,q ≥ 1, is c(p,q) = liminf(log H(n)/log n) strictly increasing in q?

OPEN (graph theory/Ramsey theory problem)

*Reference:* [erdosproblems.com/667](https://www.erdosproblems.com/667)
-/

open scoped Topology Real

namespace Erdos667

/-- H(n) function for Ramsey theory -/
noncomputable def H (p q n : ℕ) : ℕ := sorry

/-- c(p,q) = liminf(log H(n)/log n) -/
noncomputable def c (p q : ℕ) : ℝ := sorry

/-- Is c(p,q) strictly increasing in q? -/
@[category research open, AMS 05]
theorem ramsey_limit_strictly_increasing (p : ℕ) (answer : Prop) :
    answer ↔ ∀ q₁ q₂ : ℕ, q₁ < q₂ → c p q₁ < c p q₂ := by
  sorry

end Erdos667
