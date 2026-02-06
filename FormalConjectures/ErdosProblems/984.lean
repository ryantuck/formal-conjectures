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
# Erdős Problem 984

2-coloring with bounded monochromatic APs.

PROVED

*Reference:* [erdosproblems.com/984](https://www.erdosproblems.com/984)
-/

open Finset

open scoped Topology Real

namespace Erdos984

/-- 2-coloring of naturals with small monochromatic APs -/
@[category research solved, AMS 05]
theorem two_coloring_bounded_ap :
    ∃ (c : ℕ → Fin 2),
      ∀ (a d k : ℕ), d > 0 →
        (∀ i < k, c (a + i * d) = c a) →
        ∀ ε > 0, ∃ (C : ℝ), ∀ i < k, (a + i * d : ℝ) ^ ε ≤ C * k := by
  sorry

end Erdos984
