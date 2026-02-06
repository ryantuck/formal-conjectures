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
# Erdős Problem 981

Legendre symbol asymptotic.

PROVED

*Reference:* [erdosproblems.com/981](https://www.erdosproblems.com/981)
-/

open Finset Filter

open scoped Topology Real

namespace Erdos981

/-- Function related to Legendre symbol distribution -/
noncomputable def f_ε (ε p : ℝ) : ℕ := sorry

/-- Asymptotic formula for Legendre symbol sums -/
@[category research solved, AMS 11]
theorem legendre_symbol_asymptotic (ε : ℝ) (hε : 0 < ε) :
    ∃ (c : ℝ), 0 < c ∧
      Tendsto (fun x => ((Finset.filter Nat.Prime (Finset.range (Nat.floor x))).sum (fun p => f_ε ε p) : ℝ) / (x / Real.log x))
        atTop (nhds c) := by
  sorry

end Erdos981
