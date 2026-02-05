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
# Erdős Problem 519: Turán's Power Sum Problem

Let z₁,...,zₙ ∈ ℂ with z₁=1. Must there exist an absolute constant c>0 such that
max_{1≤k≤n} |∑ᵢ zᵢᵏ| > c?

SOLVED: Atkinson (1961) proved c=1/6 works; Biró improved to c>1/2.

*Reference:* [erdosproblems.com/519](https://www.erdosproblems.com/519)
-/

open BigOperators Complex

namespace Erdos519

/-- Turán's power sum lower bound -/
@[category research solved, AMS 30]
theorem turan_power_sum :
    ∃ c > 0, ∀ (n : ℕ) (hn : n > 0) (z : Fin n → ℂ), z ⟨0, hn⟩ = 1 →
      ∃ k : Fin n, ‖∑ i : Fin n, (z i) ^ (k : ℕ)‖ > c := by
  sorry

end Erdos519
