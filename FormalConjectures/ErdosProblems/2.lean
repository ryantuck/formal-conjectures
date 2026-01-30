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
import FormalConjecturesForMathlib.NumberTheory.CoveringSystem
import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Erdős Problem 2

*Reference:* [erdosproblems.com/2](https://www.erdosproblems.com/2)
-/

namespace Erdos2

open scoped BigOperators

/--
For any $C > 0$, does there exist a covering system of congruences with distinct moduli
$n_1 < n_2 < \dots < n_k$ such that $n_1 > C$?

Hough [Ho15] proved that the answer is negative; the minimum modulus of a covering system
with distinct moduli is bounded.

[Ho15] R. Hough, _Solution of the minimum modulus problem for covering systems_.
Annals of Mathematics (2015), 181(1), 361-382.
-/
@[category research solved, AMS 11]
theorem erdos_2 : answer(False) ↔ ∀ C : ℕ, ∃ (c : StrictCoveringSystem ℤ),
    ∀ i, (Submodule.IsPrincipal.generator (c.moduli i)).natAbs > C := by
  sorry

/--
Hough [Ho15] proved that the minimum modulus of a covering system with distinct moduli
is at most $10^{16}$.
-/
@[category research solved, AMS 11]
theorem erdos_2.variants.bound : ∀ (c : StrictCoveringSystem ℤ),
    ∃ i, (Submodule.IsPrincipal.generator (c.moduli i)).natAbs ≤ 10 ^ 16 := by
  sorry

/--
Balister, Bollobás, Morris, Sahasrabudhe, and Tiba [BB+22] improved the bound on the
minimum modulus to $616,000$.

[BB+22] Balister, P., Bollobás, B., Morris, R., Sahasrabudhe, J., and Tiba, M.,
_On the j-th smallest modulus of a covering system with distinct moduli_.
Geometry & Topology (2022), 26(2), 509-561.
-/
@[category research solved, AMS 11]
theorem erdos_2.variants.bound_strong : ∀ (c : StrictCoveringSystem ℤ),
    ∃ i, (Submodule.IsPrincipal.generator (c.moduli i)).natAbs ≤ 616000 := by
  sorry

/--
Does there exist a covering system with distinct odd moduli all greater than $1$?

The Erdős–Selfridge conjecture posits that the answer is negative.
-/
@[category research open, AMS 11]
theorem erdos_2.variants.odd : answer(False) ↔ ∃ (c : StrictCoveringSystem ℤ),
    (∀ i, (Submodule.IsPrincipal.generator (c.moduli i)).natAbs % 2 = 1) ∧
    (∀ i, (Submodule.IsPrincipal.generator (c.moduli i)).natAbs > 1) := by
  sorry

/--
Does there exist a covering system with distinct, odd, square-free moduli all greater than $1$?

Hough and Nielsen [HoNi19] proved that any covering system with distinct moduli greater than $1$
must contain a modulus divisible by $2$ or $3$, which implies a negative answer for square-free
odd moduli.

[HoNi19] Hough, R. and Nielsen, P. P., _Covering systems with restricted divisibility_.
Duke Mathematical Journal (2019), 168(11), 2129-2195.
-/
@[category research solved, AMS 11]
theorem erdos_2.variants.odd_squarefree : answer(False) ↔ ∃ (c : StrictCoveringSystem ℤ),
    (∀ i, (Submodule.IsPrincipal.generator (c.moduli i)).natAbs % 2 = 1) ∧
    (∀ i, (Submodule.IsPrincipal.generator (c.moduli i)).natAbs > 1) ∧
    (∀ i, Squarefree (Submodule.IsPrincipal.generator (c.moduli i)).natAbs) := by
  sorry

end Erdos2
