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
# Erdős Problem 928

Density of integers with smooth consecutive values.

OPEN

*Reference:* [erdosproblems.com/928](https://www.erdosproblems.com/928)
-/

open Finset Filter

open scoped Topology Real

namespace Erdos928

/-- Density of n where both n and n+1 have all prime factors ≤ y -/
@[category research open, AMS 11]
theorem smooth_consecutive_density (answer : Prop) :
    answer ↔ ∃ (f : ℕ → ℝ), ∀ y : ℕ,
      Tendsto (fun x => (Finset.filter (fun n =>
        (∀ p : ℕ, p.Prime → p ∣ n → p ≤ y) ∧
        (∀ p : ℕ, p.Prime → p ∣ (n + 1) → p ≤ y)) (Finset.range x)).card / x)
      atTop (nhds (f y)) := by
  sorry

end Erdos928
