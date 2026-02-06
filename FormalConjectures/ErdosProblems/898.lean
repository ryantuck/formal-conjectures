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
# Erdős Problem 898

Erdős-Mordell inequality.

PROVED

*Reference:* [erdosproblems.com/898](https://www.erdosproblems.com/898)
-/

open EuclideanSpace Metric

open scoped Topology Real

namespace Erdos898

/-- Erdős-Mordell inequality -/
@[category research solved, AMS 52]
theorem erdos_mordell_inequality :
    ∀ (A B C P : Fin 2 → ℝ),
      sorry →
      dist P A + dist P B + dist P C ≥ 2 * sorry := by
  sorry

end Erdos898
