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
# Erdős Problem 629

What is the minimal number of vertices n(k) such that there exists a bipartite graph G
with list chromatic number χ_L(G) > k?

OPEN

*Reference:* [erdosproblems.com/629](https://www.erdosproblems.com/629)
-/

open SimpleGraph

open scoped Topology Real

namespace Erdos629

variable {α : Type*}

/-- List chromatic number of a graph -/
noncomputable def listChromaticNumber (G : SimpleGraph α) : ℕ := sorry

/-- Minimal vertices for bipartite graph with χ_L(G) > k -/
noncomputable def n (k : ℕ) : ℕ := sorry

/-- n(k) is the minimal number of vertices for bipartite G with χ_L(G) > k -/
@[category research open, AMS 05]
theorem min_vertices_list_chromatic (k : ℕ) :
    n k = sorry := by
  sorry

end Erdos629
