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
import FormalConjecturesForMathlib.Data.Set.Density

/-!
# Erdős Problem 16

*Reference:* [erdosproblems.com/16](https://www.erdosproblems.com/16)
-/

namespace Erdos16

open Nat

/--
The set of odd integers not of the form $2^k + p$.
-/
def S : Set ℕ := {n | Odd n ∧ ∀ k p, p.Prime → n ≠ 2^k + p}

/--
Is the set of odd integers not of the form $2^k + p$ the union of an infinite arithmetic
progression and a set of density $0$?

Erdős [Er50] proved that $S$ contains an infinite arithmetic progression.
Chen [Ch23] proved that the answer to the question is no.

[Er50] P. Erdős, _On integers of the form $2^k + p$ and some related problems_, Summa Brasil. Math. 2 (1950), 113–123.
[Ch23] Y. G. Chen, _On the set of odd integers not of the form $2^k + p$_, 2023.
-/
@[category research solved, AMS 11]
theorem erdos_16 : answer(False) ↔ ∃ (a d : ℕ) (Z : Set ℕ),
    d ≠ 0 ∧
    (∀ n, a + n * d ∈ S) ∧
    Z.HasDensity 0 ∧
    S = {n | ∃ k, n = a + k * d} ∪ Z := by
  sorry

end Erdos16
