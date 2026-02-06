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
# Erdős Problem 1146

Is B = {2^m3^n : m,n ≥ 0} an essential component?

OPEN

*Reference:* [erdosproblems.com/1146](https://www.erdosproblems.com/1146)
-/

open Finset Filter

open scoped Topology Real

namespace Erdos1146

/-- Powers of 2 and 3 as essential component -/
@[category research open, AMS 11]
theorem powers_two_three_essential (answer : Prop) :
    answer ↔ sorry := by
  sorry

end Erdos1146
