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
# Erdős Problem 824

h(x) counts coprime pairs with equal sigma.

OPEN

*Reference:* [erdosproblems.com/824](https://www.erdosproblems.com/824)
-/

open Finset Nat

open scoped Topology Real

namespace Erdos824

/-- Sum of divisors -/
def sigma (n : ℕ) : ℕ := sorry

/-- h(x): count coprime pairs a<b<x with σ(a)=σ(b) -/
noncomputable def h (x : ℝ) : ℕ := sorry

/-- Is h(x) > x^(2-o(1))? -/
@[category research open, AMS 11]
theorem coprime_equal_sigma (answer : Prop) :
    answer ↔ ∀ᶠ (x : ℝ) in Filter.atTop,
      h x > x ^ (2 - sorry) := by
  sorry

end Erdos824
