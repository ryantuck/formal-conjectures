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
# Erdős Problem 669

Estimate F_k(n) (minimal lines through ≥ k points) and f_k(n) (minimal lines through exactly k points).
Determine lim F_k(n)/n² and lim f_k(n)/n².

OPEN (Orchard problem when k=3: both ~ n²/6)

*Reference:* [erdosproblems.com/669](https://www.erdosproblems.com/669)
-/

open Finset

open scoped Topology Real

namespace Erdos669

/-- F_k(n): minimal lines through ≥ k points -/
noncomputable def F_k (k n : ℕ) : ℕ := sorry

/-- f_k(n): minimal lines through exactly k points -/
noncomputable def f_k (k n : ℕ) : ℕ := sorry

/-- Determine lim F_k(n)/n² -/
@[category research open, AMS 52]
theorem F_k_asymptotic (k : ℕ) :
    ∃ L : ℝ, Filter.Tendsto (fun n => (F_k k n : ℝ) / n^2) Filter.atTop (nhds L) := by
  sorry

end Erdos669
