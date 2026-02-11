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
# Erdős Problem 1150

Ultraflat polynomials with ±1 coefficients.

OPEN

*Reference:* [erdosproblems.com/1150](https://www.erdosproblems.com/1150)
-/

open Finset Filter

open scoped Topology Real

namespace Erdos1150

/-- Question about the existence of ultraflat polynomials with ±1 coefficients.

    An ultraflat polynomial is one where the absolute value remains bounded on some
    region (typically a curve or arc). The problem asks whether such polynomials
    exist with all coefficients being ±1.

    Note: Without a precise definition of "ultraflat" and the specific properties
    being asked about, this is a placeholder formalization. -/
@[category research open, AMS 26]
theorem ultraflat_polynomials :
    answer(sorry) ↔
      ∃ (P : ℕ → Polynomial ℂ),
        (∀ n i, (P n).coeff i ∈ ({-1, 1} : Set ℂ)) ∧
        True := by
  sorry

end Erdos1150
