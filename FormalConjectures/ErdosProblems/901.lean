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
# Erdős Problem 901

Minimum edges in n-uniform 3-chromatic hypergraph.

OPEN

*Reference:* [erdosproblems.com/901](https://www.erdosproblems.com/901)
-/

open Finset

open scoped Topology Real

namespace Erdos901

/-- Chromatic number -/
noncomputable def chromaticNumber (H : Finset (Finset α)) : ℕ := sorry

/-- m(n): minimum edges in n-uniform 3-chromatic hypergraph without Property B -/
noncomputable def m (n : ℕ) : ℕ := sorry

/-- Estimate m(n) -/
@[category research open, AMS 05]
theorem uniform_chromatic_min_edges :
    sorry := by
  sorry

end Erdos901
