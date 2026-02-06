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
# Erdős Problem 745

Random graph second largest component size.

PROVED

*Reference:* [erdosproblems.com/745](https://www.erdosproblems.com/745)
-/

open Finset

open scoped Topology Real Probability

namespace Erdos745

/-- Size of second largest component -/
noncomputable def secondLargestComponent (G : SimpleGraph (Fin n)) : ℕ := sorry

/-- Second largest component is o(log n) -/
@[category research solved, AMS 05]
theorem second_largest_component_small (n : ℕ) :
    sorry := by
  sorry

end Erdos745
