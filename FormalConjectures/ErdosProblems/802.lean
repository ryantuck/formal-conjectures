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
# Erdős Problem 802

K_r-free graph independence bound.

OPEN

*Reference:* [erdosproblems.com/802](https://www.erdosproblems.com/802)
-/

open Finset

open scoped Topology Real

namespace Erdos802

variable {α : Type*}

/-- Independence number -/
noncomputable def independenceNumber (G : SimpleGraph α) : ℕ := sorry

/-- K_r-free with average degree t has large independent set -/
@[category research open, AMS 05]
theorem kr_free_independence (r : ℕ) (answer : Prop) :
    answer ↔ ∃ c : ℝ, c > 0 ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] [G.LocallyFinite] (t : ℝ),
        G.CliqueFree r →
        (Finset.univ.sum fun v => (G.degree v : ℝ)) / (2 * n) = t →
        independenceNumber G ≥ c * (Real.log t / t) * n := by
  sorry

end Erdos802
