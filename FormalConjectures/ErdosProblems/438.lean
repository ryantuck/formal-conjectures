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
# Erdős Problem 438

How large can A ⊆ {1,...,N} be if A+A contains no square numbers?

Massias: Lower bound |A| ≥ (11/32)N using residues modulo 32.

Khalfalah-Lodha-Szemerédi: SOLVED - Sharp asymptotic |A| ≤ ((11/32) + o(1))N.

*Reference:* [erdosproblems.com/438](https://www.erdosproblems.com/438)
-/

open Filter Topology BigOperators Real

namespace Erdos438

/-- Maximum size of subset avoiding squares in sumset -/
noncomputable def maxSquareFree (N : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ A : Finset ℕ, A.card = k ∧ (∀ a ∈ A, 0 < a ∧ a ≤ N) ∧
    ∀ a ∈ A, ∀ b ∈ A, ∀ n : ℕ, a + b ≠ n ^ 2}

/-- Khalfalah-Lodha-Szemerédi: Sharp asymptotic bound -/
@[category research solved, AMS 11]
theorem erdos_438_kls :
    Tendsto (fun N : ℕ => (maxSquareFree N : ℝ) / N) atTop (𝓝 (11/32)) := by
  sorry

/-- Massias: Lower bound construction -/
@[category research solved, AMS 11]
theorem erdos_438_massias :
    ∀ N : ℕ, N ≥ 1 → (maxSquareFree N : ℝ) ≥ (11/32 : ℝ) * N - 1 := by
  sorry

end Erdos438
