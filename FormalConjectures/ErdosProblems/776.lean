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
# Erdős Problem 776

Set family with repeated sizes.

OPEN

*Reference:* [erdosproblems.com/776](https://www.erdosproblems.com/776)
-/

open Finset

open scoped Topology Real

namespace Erdos776

/-- Minimal n for n-3 distinct sizes with r repetitions -/
@[category research open, AMS 05]
theorem set_family_repeated_sizes (r : ℕ) (hr : r ≥ 2) (answer : Prop) :
    answer ↔ ∃ n : ℕ, ∀ (F : Finset (Finset ℕ)),
      (∀ t : ℕ, (F.filter (fun A => A.card = t)).card ≥ r ∨
        (F.filter (fun A => A.card = t)).card = 0) →
      sorry := by
  sorry

end Erdos776
