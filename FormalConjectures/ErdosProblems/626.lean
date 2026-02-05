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
# Erdős Problem 626

Does the limit of g_k(n) / log n exist as n → ∞ (where g_k(n) is the largest girth
achievable by an n-vertex graph with chromatic number k)?

OPEN

*Reference:* [erdosproblems.com/626](https://www.erdosproblems.com/626)
-/

open SimpleGraph

open scoped Topology Real

namespace Erdos626

/-- g_k(n): largest girth for n-vertex graph with chromatic number k -/
noncomputable def g_k (k n : ℕ) : ℕ := sorry

/-- Does lim g_k(n) / log n exist? -/
@[category research open, AMS 05]
theorem girth_chromatic_limit_exists (k : ℕ) (answer : Prop) :
    answer ↔ ∃ L : ℝ, Filter.Tendsto (fun n => (g_k k n : ℝ) / Real.log n)
      Filter.atTop (nhds L) := by
  sorry

end Erdos626
