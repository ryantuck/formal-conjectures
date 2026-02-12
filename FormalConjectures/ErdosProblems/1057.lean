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
# Erdős Problem 1057

Growth rate of Carmichael numbers.

OPEN

STATUS: OPEN

*Reference:* [erdosproblems.com/1057](https://www.erdosproblems.com/1057)
-/

open Finset Filter

open scoped Topology Real

namespace Erdos1057

/--
English version:  Carmichael number predicate -/
def isCarmichael (n : ℕ) : Prop :=
  ¬ n.Prime ∧ n > 1 ∧ ∀ a : ℕ, Nat.Coprime a n → a ^ (n - 1) ≡ 1 [MOD n]

/--
English version:  -/
@[category research open, AMS 11]
theorem carmichael_growth :
    ∃ (C : ℕ → ℕ), StrictMono C ∧
      (∀ n, isCarmichael (C n)) ∧
      Filter.Tendsto (fun n => (C (n + 1) : ℝ) / C n)
        Filter.atTop (nhds 1) := by
  sorry

end Erdos1057
