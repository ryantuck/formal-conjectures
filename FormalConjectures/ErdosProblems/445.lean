/-
Copyright 2025 The Formal Conjectures Authors.

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
# Erdős Problem 445

For any constant c > 1/2, if p is a sufficiently large prime, then for any non-negative
integer n, do there exist integers a, b in the interval (n, n+p^c) such that ab ≡ 1 (mod p)?

Heilbronn: Proved for c sufficiently close to 1.
Heath-Brown (2000): Proved for all c > 3/4.

*Reference:* [erdosproblems.com/445](https://www.erdosproblems.com/445)
-/

open Filter Topology BigOperators Real

namespace Erdos445

/-- Heath-Brown: Multiplicative inverses in short intervals -/
@[category research open, AMS 11]
theorem erdos_445_heath_brown :
    ∀ c : ℝ, c > 3/4 → ∀ᶠ p : ℕ in Filter.atTop, p.Prime →
      ∀ n : ℕ, ∃ a b : ℕ, n < a ∧ a < n + ⌊(p : ℝ) ^ c⌋₊ ∧ n < b ∧ b < n + ⌊(p : ℝ) ^ c⌋₊ ∧
        (a : ZMod p) * b = 1 := by
  sorry

end Erdos445
