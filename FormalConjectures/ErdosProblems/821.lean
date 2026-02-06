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
# Erdős Problem 821

g(n) counts m with φ(m)=n.

OPEN (best bound g(n) > n^0.71568)

*Reference:* [erdosproblems.com/821](https://www.erdosproblems.com/821)
-/

open Finset Nat

open scoped Topology Real

namespace Erdos821

/-- g(n): count of m with φ(m) = n -/
noncomputable def g (n : ℕ) : ℕ := sorry

/-- Is g(n) > n^(1-ε) for infinitely many n? -/
@[category research open, AMS 11]
theorem euler_phi_inverse (answer : Prop) :
    answer ↔ ∀ (ε : ℝ), ε > 0 →
      ∃ᶠ (n : ℕ) in Filter.atTop, g n > (n : ℝ) ^ (1 - ε) := by
  sorry

end Erdos821
