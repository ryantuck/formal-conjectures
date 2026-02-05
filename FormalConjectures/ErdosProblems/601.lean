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
# Erdős Problem 601

For which limit ordinals α is it true that every graph with vertex set α must contain
either an infinite path or an independent set of order type α?

OPEN

*Reference:* [erdosproblems.com/601](https://www.erdosproblems.com/601)
-/

open SimpleGraph Ordinal Cardinal

open scoped Topology Real

namespace Erdos601

/-- Which limit ordinals α force infinite paths or independent sets of order type α? -/
@[category research open, AMS 03]
theorem limit_ordinal_path_or_independent (α : Ordinal.{0}) (hlimit : α.IsLimit) (answer : Prop) :
    answer ↔ ∀ (G : SimpleGraph α.toType),
      (∃ (path : Set α.toType), sorry) ∨
      (∃ (indep : Set α.toType), sorry) := by
  sorry

end Erdos601
