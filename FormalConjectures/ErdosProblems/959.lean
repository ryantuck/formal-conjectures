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
# Erdős Problem 959

Distance frequency estimation in finite point sets.

OPEN

*Reference:* [erdosproblems.com/959](https://www.erdosproblems.com/959)
-/

open Finset Filter

open scoped Topology Real

namespace Erdos959

/-- Maximum difference between top distance frequencies -/
@[category research open, AMS 52]
theorem distance_frequency_gap (answer : Prop) :
    answer ↔ ∃ (g : ℕ → ℝ),
      ∀ n : ℕ, ∃ (A : Finset (ℝ × ℝ)),
        A.card = n ∧
        let dists := (A.product A |>.filter (fun (p, q) => p ≠ q) |>.image (fun (p, q) => dist p q)).sort (· ≥ ·)
        let f := fun d => (A.product A |>.filter (fun (p, q) => dist p q = d)).card
        g n ≤ |f (dists.get! 0) - f (dists.get! 1)| := by
  sorry

end Erdos959
