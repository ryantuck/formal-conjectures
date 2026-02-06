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
# Erdős Problem 950

Function involving primes and gaps.

OPEN

*Reference:* [erdosproblems.com/950](https://www.erdosproblems.com/950)
-/

open Finset Filter

open scoped Topology Real

namespace Erdos950

/-- Function f(n) = Σ(p<n) 1/(n-p) for primes p -/
noncomputable def f (n : ℕ) : ℝ :=
  (Finset.filter Nat.Prime (Finset.range n)).sum (fun p => 1 / (n - p : ℝ))

/-- Growth properties of f -/
@[category research open, AMS 11]
theorem f_limit_properties (answer : Prop) :
    answer ↔ (liminf f atTop = 1 ∧ limsup f atTop = ⊤) ∧
      (∀ n : ℕ, f n = o(fun n => Real.log (Real.log n))) := by
  sorry

end Erdos950
