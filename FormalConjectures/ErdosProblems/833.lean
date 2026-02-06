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
# Erdős Problem 833

Hypergraph chromatic 3 vertex degree.

SOLVED

*Reference:* [erdosproblems.com/833](https://www.erdosproblems.com/833)
-/

open Finset

open scoped Topology Real

namespace Erdos833

/-- Chromatic number -/
noncomputable def chromaticNumber (H : Finset (Finset α)) : ℕ := sorry

/-- Chromatic 3 has vertex in (1+c)^r edges -/
@[category research solved, AMS 05]
theorem chromatic_three_vertex_degree :
    ∃ c : ℝ, c > 0 ∧
      ∀ (r : ℕ) (H : Finset (Finset α)),
        (∀ e ∈ H, e.card = r) →
        chromaticNumber H = 3 →
        ∃ (v : α), (H.filter (fun e => v ∈ e)).card ≥ (1 + c) ^ r := by
  sorry

end Erdos833
