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
# Erdős Problem 1148

Representation as sum/difference of squares.

OPEN

*Reference:* [erdosproblems.com/1148](https://www.erdosproblems.com/1148)
-/

open Finset Filter

open scoped Topology Real

namespace Erdos1148

/-- Representation as sum or difference of squares -/
@[category research open, AMS 11]
theorem sum_difference_squares :
    ∀ n : ℕ, ∃ a b : ℕ, n = a^2 + b^2 ∨ (n : ℤ) = |(a : ℤ)^2 - (b : ℤ)^2| := by
  sorry

end Erdos1148
