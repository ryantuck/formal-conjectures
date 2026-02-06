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
# Erdős Problem 892

Primitive sequence with aₙ ≪ bₙ.

OPEN

*Reference:* [erdosproblems.com/892](https://www.erdosproblems.com/892)
-/

open Finset

open scoped Topology Real

namespace Erdos892

/-- Primitive sequence (no term divides another) -/
def IsPrimitive (a : ℕ → ℕ) : Prop := sorry

/-- Necessary and sufficient condition for primitive sequence -/
@[category research open, AMS 11]
theorem primitive_sequence_condition :
    sorry := by
  sorry

end Erdos892
