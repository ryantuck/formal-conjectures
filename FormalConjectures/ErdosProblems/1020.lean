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
# Erdős Problem 1020

Erdős matching conjecture.

OPEN

STATUS: OPEN

*Reference:* [erdosproblems.com/1020](https://www.erdosproblems.com/1020)
-/

open Finset

open scoped Topology Real

namespace Erdos1020

/--
English version:  Maximum edges in r-uniform hypergraph with no k independent edges -/
noncomputable def matchingNumber (r k n : ℕ) : ℕ := sorry

/--
English version:  -/
@[category research open, AMS 05]
theorem erdos_matching_conjecture (r k : ℕ) : answer(sorry) ↔ ∃ (f : ℕ → ℕ → ℕ),
      ∀ n : ℕ, matchingNumber r k n = f r k := by
  sorry

end Erdos1020
