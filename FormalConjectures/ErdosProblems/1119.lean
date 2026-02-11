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
# Erdős Problem 1119

Cardinality of families of entire functions.

SOLVED

*Reference:* [erdosproblems.com/1119](https://www.erdosproblems.com/1119)
-/

open Finset

open scoped Real

namespace Erdos1119

/-- Cardinality of families of entire functions.
    Result about bounding cardinality of families with special properties.
    Current formalization is a placeholder. -/
@[category research solved, AMS 30]
theorem cardinality_entire_function_families :
    ∀ (property : (ℂ → ℂ) → Prop), ∃ (n : ℕ),
      ∀ (S : Finset (ℂ → ℂ)), (∀ f ∈ S, property f) →
        S.card ≤ n := by
  sorry

end Erdos1119
