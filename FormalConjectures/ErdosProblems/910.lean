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
# Erdős Problem 910

Connected sets contain non-trivial connected subsets.

DISPROVED

*Reference:* [erdosproblems.com/910](https://www.erdosproblems.com/910)
-/

open scoped Topology Real

namespace Erdos910

/-- Disproved: connected sets in ℝⁿ contain non-trivial connected subsets -/
@[category research solved, AMS 52]
theorem not_connected_subsets :
    ¬ ∀ (n : ℕ) (S : Set (Fin n → ℝ)),
      IsConnected S →
      ∃ (T : Set (Fin n → ℝ)),
        T ⊂ S ∧ T.Nonempty ∧ IsConnected T := by
  sorry

end Erdos910
