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
# Erdős Problem 711

Prove bounds for f(n,m) - divisibility with parameter m.

OPEN (1000 rupees reward)

*Reference:* [erdosproblems.com/711](https://www.erdosproblems.com/711)
-/

open Finset Nat

open scoped Topology Real

namespace Erdos711

/-- f(n,m): minimal interval length with parameter m -/
noncomputable def f (n m : ℕ) : ℕ := sorry

/-- Bound max_m f(n,m) ≤ n^(1+o(1)) -/
@[category research open, AMS 11]
theorem max_f_bound (answer : Prop) :
    answer ↔ ∀ᶠ (n : ℕ) in Filter.atTop,
      ∀ m : ℕ, f n m ≤ n * (n : ℝ) ^ (1/100 : ℝ) := by
  sorry

/-- max_m (f(n,m) - f(n,n)) → ∞ -/
@[category research open, AMS 11]
theorem max_f_difference_unbounded (answer : Prop) :
    answer ↔ Filter.Tendsto
      (fun n => sSup {f n m - f n n | m : ℕ})
      Filter.atTop Filter.atTop := by
  sorry

end Erdos711
