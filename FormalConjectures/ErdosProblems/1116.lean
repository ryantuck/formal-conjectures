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
# Erdős Problem 1116

Meromorphic functions and root distribution.

SOLVED

*Reference:* [erdosproblems.com/1116](https://www.erdosproblems.com/1116)
-/

open Finset

open scoped Real

namespace Erdos1116

/-- There exists an entire function f such that for every pair of
    distinct complex values a ≠ b,
    lim sup_{r→∞} n(r,a)/n(r,b) = ∞
    where n(r,a) is the number of roots of f(z) = a in the disc |z| < r.
    Proved by Gol'dberg and Toppila independently. -/
@[category research solved, AMS 30]
theorem meromorphic_root_distribution :
    ∃ (f : ℂ → ℂ), Differentiable ℂ f ∧
      ∀ (a b : ℂ), a ≠ b →
        let n : ℝ → ℂ → ℕ := fun r c =>
          Nat.card {z : ℂ | ‖z‖ < r ∧ f z = c}
        Filter.atTop.limsup
          (fun r : ℝ => (n r a : ℝ) / (n r b : ℝ))
          = ⊤ := by
  sorry

end Erdos1116
