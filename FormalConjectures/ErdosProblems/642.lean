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
# Erdős Problem 642

For graphs where all cycles have more vertices than chords, is f(n) ≪ n?

OPEN

*Reference:* [erdosproblems.com/642](https://www.erdosproblems.com/642)
-/

open SimpleGraph

open scoped Topology Real

namespace Erdos642

/-- f(n) for graphs where cycles have more vertices than chords -/
noncomputable def f (n : ℕ) : ℕ := sorry

/-- Is f(n) ≪ n for such graphs? -/
@[category research open, AMS 05]
theorem cycles_more_vertices_than_chords (answer : Prop) :
    answer ↔ ∀ ε > 0, ∀ᶠ (n : ℕ) in Filter.atTop,
      (f n : ℝ) < ε * n := by
  sorry

end Erdos642
