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
# Erdős Problem 7

*Reference:* [erdosproblems.com/7](https://www.erdosproblems.com/7)
-/

namespace Erdos7

open scoped BigOperators

/--
Is there a covering system of congruences with distinct moduli such that all moduli are odd?

This is known as the Erdős–Selfridge conjecture (sometimes also attributed to Schinzel).
Erdős offered $25 for a proof that no such system exists, while Selfridge offered $2000 for an
explicit example.
-/
@[category research open, AMS 11]
theorem erdos_7 : answer(False) ↔ ∃ (c : StrictCoveringSystem ℤ),
    (∀ i, (Submodule.IsPrincipal.generator (c.moduli i)).natAbs % 2 = 1) ∧
    (∀ i, (Submodule.IsPrincipal.generator (c.moduli i)).natAbs > 1) := by
  sorry

/--
The answer is known to be negative if we additionally require the moduli to be square-free.
Proved by Balister, Bollobás, Morris, Sahasrabudhe, and Tiba [BBMST22].

[BBMST22] Balister, P., Bollobás, B., Morris, R., Sahasrabudhe, J., and Tiba, M.,
_On the j-th smallest modulus of a covering system with distinct moduli_.
Geometry & Topology (2022), 26(2), 509-561.
-/
@[category research solved, AMS 11]
theorem erdos_7.variants.squarefree : ¬ ∃ (c : StrictCoveringSystem ℤ),
    (∀ i, (Submodule.IsPrincipal.generator (c.moduli i)).natAbs % 2 = 1) ∧
    (∀ i, (Submodule.IsPrincipal.generator (c.moduli i)).natAbs > 1) ∧
    (∀ i, Squarefree (Submodule.IsPrincipal.generator (c.moduli i)).natAbs) := by
  sorry

end Erdos7
