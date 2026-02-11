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
# Erdős Problem 1146

Is B = {2^m3^n : m,n ≥ 0} an essential component?

This problem asks whether the set B of all numbers of the form 2^m · 3^n
(for non-negative integers m, n) is an "essential component" in the context
of additive number theory. A set is typically called an essential component
if removing it from certain additive structures fundamentally changes their
properties. The precise definition in this context requires clarification from
the original source.

OPEN

*Reference:* [erdosproblems.com/1146](https://www.erdosproblems.com/1146)
-/

namespace Erdos1146

/-- The set of numbers of the form 2^m · 3^n is an essential component.
    The precise definition of "essential component" requires further investigation
    from the original problem statement. -/
@[category research open, AMS 11]
theorem powers_two_three_essential :
    let B := {n : ℕ | ∃ m k : ℕ, n = 2^m * 3^k}
    answer(sorry) ↔ (∀ A : Set ℕ, Set.Infinite A → A ∩ B ≠ ∅) := by
  sorry

end Erdos1146
