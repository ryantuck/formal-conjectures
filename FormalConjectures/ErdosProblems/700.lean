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
# Erdős Problem 700

Characterize composite n where f(n) = n/P(n) and related questions.

OPEN

*Reference:* [erdosproblems.com/700](https://www.erdosproblems.com/700)
-/

open Nat

open scoped Topology Real

namespace Erdos700

/-- P(n): largest prime divisor of n -/
noncomputable def P (n : ℕ) : ℕ := sorry

/-- f(n) = n/P(n) -/
noncomputable def f (n : ℕ) : ℚ := n / (P n)

/-- Characterize composite n with specific properties of f(n) -/
@[category research open, AMS 11]
theorem characterize_composite_f_property :
    ∃ predicate : ℕ → Prop, ∀ n : ℕ, ¬ n.Prime →
      predicate n ↔ sorry := by
  sorry

end Erdos700
