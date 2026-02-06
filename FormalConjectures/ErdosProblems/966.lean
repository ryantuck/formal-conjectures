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
# Erdős Problem 966

Arithmetic progressions and Ramsey theory.

PROVED

*Reference:* [erdosproblems.com/966](https://www.erdosproblems.com/966)
-/

open Finset

open scoped Topology Real

namespace Erdos966

/-- AP-free set with Ramsey property -/
@[category research solved, AMS 05]
theorem ap_free_ramsey (k r : ℕ) :
    ∃ (A : Set ℕ),
      (∀ (a d : ℕ), d > 0 → ¬ ∀ i < k + 1, a + i * d ∈ A) ∧
      (∀ (c : A → Fin r),
        ∃ (a d : ℕ), d > 0 ∧
          (∀ i < k, a + i * d ∈ A) ∧
          (∀ i j : ℕ, i < k → j < k → c ⟨a + i * d, sorry⟩ = c ⟨a + j * d, sorry⟩)) := by
  sorry

end Erdos966
