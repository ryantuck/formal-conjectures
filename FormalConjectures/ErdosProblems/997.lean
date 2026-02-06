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
# Erdős Problem 997

Well-distribution of prime lacunary sequences.

OPEN

*Reference:* [erdosproblems.com/997](https://www.erdosproblems.com/997)
-/

open Finset Filter

open scoped Topology Real

namespace Erdos997

/-- Prime sequence not well-distributed -/
@[category research open, AMS 11]
theorem prime_not_well_distributed (answer : Prop) :
    answer ↔ ∀ α : ℝ, Irrational α →
      let p := fun n => (Finset.filter Nat.Prime (Finset.range sorry)).toList.get! n
      ¬ sorry := by
  sorry

end Erdos997
