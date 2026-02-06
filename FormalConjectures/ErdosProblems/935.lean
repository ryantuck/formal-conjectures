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
# Erdős Problem 935

Growth of the powerful part of products of consecutive integers.

OPEN

*Reference:* [erdosproblems.com/935](https://www.erdosproblems.com/935)
-/

open Finset Filter

open scoped Topology Real

namespace Erdos935

/-- Powerful part of a number -/
noncomputable def powerfulPart (n : ℕ) : ℕ := sorry

/-- Growth of powerful part of factorial-like products -/
@[category research open, AMS 11]
theorem powerful_part_product_growth (k : ℕ) (answer : Prop) :
    answer ↔ Tendsto (fun n =>
      Real.log (powerfulPart (Finset.range k |>.prod (fun i => n + i))) / Real.log n)
      atTop atTop := by
  sorry

end Erdos935
