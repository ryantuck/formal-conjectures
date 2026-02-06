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
# Erdős Problem 673

Let 1=d₁<...<d_τ(n)=n be divisors of n and G(n) = Σ d_i/d_{i+1}.
Is G(n)→∞ for almost all n? Can one prove an asymptotic formula for Σ_{n≤X} G(n)?

PROVED: Tao established bounds; Erdős-Tenenbaum proved distribution

*Reference:* [erdosproblems.com/673](https://www.erdosproblems.com/673)
-/

open Nat

open scoped Topology Real

namespace Erdos673

/-- G(n) = sum of ratios of consecutive divisors -/
noncomputable def G (n : ℕ) : ℝ := sorry

/-- G(n) → ∞ for almost all n -/
@[category research solved, AMS 11]
theorem G_tends_infinity_almost_all :
    ∀ ε > 0, Filter.Tendsto
      (fun X => (Finset.range X).filter (fun n => G n < sorry) |>.card / X)
      Filter.atTop (nhds 0) := by
  sorry

end Erdos673
