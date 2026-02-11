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
# Erdős Problem 1178

Brown-Erdős-Sós hypergraph conjecture.

OPEN

*Reference:* [erdosproblems.com/1178](https://www.erdosproblems.com/1178)
-/

open Finset Filter Asymptotics

open scoped Topology Real

namespace Erdos1178

/-- For r ≥ 3, let d_r(e) denote the minimal d such that ex_r(n, F) = o(n²),
    where F is the family of r-uniform hypergraphs on d vertices with e edges.

    Brown-Erdős-Sós Conjecture: d_r(e) = (r-2)e + 3 for all r, e ≥ 3.

    Known results:
    - d_r(3) = (r-2)·3 + 3 for all r ≥ 3 (Erdős, Frankl, Rödl)
    - d_3(e) ≤ e + O(log e / log log e) (Conlon et al., 2023)
    - d_r(e) ≤ (r-2)e + 2 + ⌊log₂ e⌋ (Sárközy, Selkow)

    This formalization states the conjectured exact formula. -/
@[category research open, AMS 05]
theorem brown_erdos_sos_conjecture :
    ∀ (r e : ℕ), r ≥ 3 → e ≥ 3 →
      ∃ (d_r : ℕ → ℕ), d_r e = (r - 2) * e + 3 ∧
        ∀ (d : ℕ), d < d_r e →
          ∃ (ex_r : ℕ → ℕ), (fun n => (ex_r n : ℝ)) =o[atTop] (fun n => (n : ℝ)^2) := by
  sorry

end Erdos1178
