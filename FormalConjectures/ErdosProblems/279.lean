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
# Erdős Problem 279

*Reference:* [erdosproblems.com/279](https://www.erdosproblems.com/279)
-/

open Filter Topology

namespace Erdos279

/--
For $k \geq 3$, can congruence classes $a_p \pmod{p}$ be chosen for every prime $p$ such that
all sufficiently large integers can be written as $a_p + tp$ for some prime $p$ and integer $t \geq k$?

Even the case $k=3$ appears difficult.
-/
@[category research open, AMS 11]
theorem erdos_279 (k : ℕ) (hk : k ≥ 3) :
    ∃ a : ℕ → ℕ, ∃ N : ℕ, ∀ n ≥ N,
      ∃ p : ℕ, Nat.Prime p ∧ ∃ t : ℕ, t ≥ k ∧ n = a p + t * p := by
  sorry

end Erdos279
