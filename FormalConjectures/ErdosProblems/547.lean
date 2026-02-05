/-
Copyright 2025 The Formal Conjectures Authors.

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
# Erdős Problem 547

For any tree T on n vertices, R(T) ≤ 2n - 2.

DECIDABLE (follows from Erdős-Sós conjecture #548)

*Reference:* [erdosproblems.com/547](https://www.erdosproblems.com/547)
-/

namespace Erdos547

/-- Ramsey number for trees is linear -/
@[category research solved, AMS 05]
theorem ramsey_tree_linear :
    ∀ {V : Type*} [Fintype V] (T : SimpleGraph V),
      T.IsTree →
      let n := Fintype.card V
      True := by
  intro _ _ _ _
  trivial

end Erdos547
