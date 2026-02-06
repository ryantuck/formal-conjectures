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
# Erdős Problem 900

Random graph long path near threshold.

PROVED

*Reference:* [erdosproblems.com/900](https://www.erdosproblems.com/900)
-/

open Finset

open scoped Topology Real Probability

namespace Erdos900

/-- Random graph with cn edges has long path -/
@[category research solved, AMS 05]
theorem random_graph_long_path (c : ℝ) (hc : c < 1/2) :
    ∃ f : ℝ → ℝ, Filter.Tendsto f (nhds (1/2 : ℝ)) (nhds 0) ∧
      sorry := by
  sorry

end Erdos900
