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
# Erdős Problem 8

*Reference:* [erdosproblems.com/8](https://www.erdosproblems.com/8)
-/

namespace Erdos8

open scoped BigOperators

/--
For any finite colouring of the integers, is there a covering system all of whose moduli are
monochromatic?

Erdős and Graham also asked a density-type version: for example, is
$$ \sum_{a \in A, a > N} \frac{1}{a} \gg \log N $$
a sufficient condition for $A$ to contain the moduli of a covering system?

The answer (to both colouring and density versions) is negative, due to the result of
Hough [Ho15] on the minimum size of a modulus in a covering system.

[Ho15] R. Hough, _Solution of the minimum modulus problem for covering systems_.
Annals of Mathematics (2015), 181(1), 361-382.
-/
@[category research solved, AMS 11]
theorem erdos_8 : answer(False) ↔ ∀ (C : Type*) [Fintype C] (f : ℕ → C),
    ∃ (c : StrictCoveringSystem ℤ), ∀ i j,
      f (Submodule.IsPrincipal.generator (c.moduli i)).natAbs =
      f (Submodule.IsPrincipal.generator (c.moduli j)).natAbs := by
  sorry

end Erdos8
