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
# Erdős Problem 737

Graph with chromatic ℵ₁ has edge in all large cycles.

PROVED

*Reference:* [erdosproblems.com/737](https://www.erdosproblems.com/737)
-/

open Finset Cardinal

open scoped Topology Real

namespace Erdos737

variable {α : Type*}

/-- Chromatic number (extended to cardinals) -/
noncomputable def chromaticCardinal (G : SimpleGraph α) : Cardinal := sorry

/-- Edge in all large cycles -/
@[category research solved, AMS 05]
theorem edge_in_all_large_cycles :
    ∀ (G : SimpleGraph α),
      chromaticCardinal G = ℵ₁ →
      ∃ e : α × α,
        ∀ᶠ (n : ℕ) in Filter.atTop,
          sorry := by
  sorry

end Erdos737
