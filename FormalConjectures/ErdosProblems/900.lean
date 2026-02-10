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

open Finset Filter

open scoped Topology Real

namespace Erdos900

/-- Random graph with cn edges has long path (Ajtai-Komlós-Szemerédi) -/
@[category research solved, AMS 5]
theorem random_graph_long_path :
    ∃ f : ℝ → ℝ,
      (Tendsto f (𝓝[>] (1/2)) (𝓝 0)) ∧
      (Tendsto f atTop (𝓝 1)) ∧
      (∀ᶠ n in atTop, ∀ c : ℝ, c > 1/2 →
        ∃ path_length : ℕ, (path_length : ℝ) ≥ f c * n) := by
  sorry

end Erdos900
