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
# Erdős Problem 967

Prime products and non-vanishing sums.

DISPROVED

*Reference:* [erdosproblems.com/967](https://www.erdosproblems.com/967)
-/

open Finset Filter

open scoped Topology Real

namespace Erdos967

/-- Disproved: Dirichlet series non-vanishing -/
@[category research solved, AMS 11]
theorem not_series_nonvanishing :
    ¬ ∀ (a : ℕ → ℕ), StrictMono a →
      Summable (fun k : ℕ => (1 : ℝ) / a k) →
      ∀ t : ℝ, 1 + ∑' k : ℕ, (1 : ℂ) / (a k : ℂ) ^ (1 + t * Complex.I) ≠ 0 := by
  sorry

end Erdos967
