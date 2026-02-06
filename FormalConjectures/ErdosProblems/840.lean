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
# Erdős Problem 840

Quasi-Sidon subset growth.

OPEN

*Reference:* [erdosproblems.com/840](https://www.erdosproblems.com/840)
-/

open Finset

open scoped Topology Real

namespace Erdos840

/-- Quasi-Sidon property -/
def IsQuasiSidon (A : Finset ℕ) : Prop :=
  (A + A).card = (1 + sorry) * Nat.choose A.card 2

/-- f(N): largest quasi-Sidon subset -/
noncomputable def f (N : ℕ) : ℕ := sorry

/-- Growth of f(N) -/
@[category research open, AMS 11]
theorem quasi_sidon_growth :
    sorry := by
  sorry

end Erdos840
