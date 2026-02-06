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
# Erdős Problem 799

List chromatic number for random graphs.

SOLVED

*Reference:* [erdosproblems.com/799](https://www.erdosproblems.com/799)
-/

open Finset

open scoped Topology Real

namespace Erdos799

/-- List chromatic number -/
noncomputable def listChromaticNumber (G : SimpleGraph α) : ℕ := sorry

/-- χ_L(G) ≈ n/(log n) for almost all graphs -/
@[category research solved, AMS 05]
theorem random_graph_list_chromatic :
    sorry := by
  sorry

end Erdos799
