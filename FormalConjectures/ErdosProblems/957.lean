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
# Erdős Problem 957

Product of extreme distance frequencies.

PROVED

*Reference:* [erdosproblems.com/957](https://www.erdosproblems.com/957)
-/

open Finset

open scoped Topology Real

namespace Erdos957

/-- Product of minimum and maximum distance frequencies bounded -/
@[category research solved, AMS 52]
theorem extreme_distance_product (n : ℕ) :
    ∀ (A : Finset (ℝ × ℝ)),
      A.card = n →
      let dists := A.product A |>.filter (fun (p, q) => p ≠ q) |>.image (fun (p, q) => dist p q)
      ∀ d₁ ∈ dists, ∀ d_k ∈ dists,
        (∀ d ∈ dists, d₁ ≤ d) →
        (∀ d ∈ dists, d ≤ d_k) →
        let f := fun d => (A.product A |>.filter (fun (p, q) => dist p q = d)).card
        (f d₁ : ℝ) * f d_k ≤ (9/8 + o(1)) * n ^ 2 := by
  sorry

end Erdos957
