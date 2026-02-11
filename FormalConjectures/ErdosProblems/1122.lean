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
# Erdős Problem 1122

Additive functions and monotonicity.

OPEN

*Reference:* [erdosproblems.com/1122](https://www.erdosproblems.com/1122)
-/

open Finset

open scoped Real

namespace Erdos1122

/-- Let f : N -> R be a multiplicatively additive function (f(ab) = f(a) + f(b) when gcd(a,b) = 1).
    Define A = {n >= 1 : f(n+1) < f(n)}.
    If |A ∩ [1,X]| = o(X), must f(n) = c*log(n) for some constant c? -/
@[category research open, AMS 11]
theorem additive_function_monotonicity :
    answer(sorry) ↔
      ∀ (f : ℕ → ℝ),
        (∀ a b, Nat.Coprime a b → f (a * b) = f a + f b) →
        (Filter.Tendsto (fun X : ℕ =>
          (Finset.filter (fun n => f (n + 1) < f n) (Finset.range X)).card / (X : ℝ))
          Filter.atTop (nhds 0)) →
        ∃ c : ℝ, ∀ n > 0, f n = c * Real.log n := by
  sorry

end Erdos1122
