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
# Erdős Problem 464

Let A = {n₁ < n₂ < ...} ⊂ ℕ be a lacunary sequence (nₖ₊₁ ≥ (1+ε)nₖ for all k).
Must there exist an irrational θ such that {‖θ·nₖ‖ : k ≥ 1} is not dense in [0,1],
where ‖x‖ denotes the distance to the nearest integer?

de Mathan-Pollington: PROVED - For any lacunary A, there exists θ with
  inf_k ‖θ·nₖ‖ ≫ ε⁴/log(1/ε)

Peres-Schlag: Improved to inf_k ‖θ·nₖ‖ ≫ ε/log(1/ε)

*Reference:* [erdosproblems.com/464](https://www.erdosproblems.com/464)
-/

open Filter Topology BigOperators Real Classical

namespace Erdos464

/-- Distance to nearest integer -/
noncomputable def distInt (x : ℝ) : ℝ :=
  min (x - ⌊x⌋) (⌈x⌉ - x)

/-- de Mathan-Pollington: Non-dense orbits exist -/
@[category research solved, AMS 11]
theorem erdos_464_de_mathan_pollington :
    ∀ ε : ℝ, ε > 0 → ∀ seq : ℕ → ℕ, StrictMono seq →
      (∀ k : ℕ, (seq (k + 1) : ℝ) ≥ (1 + ε) * seq k) →
      ∃ θ : ℝ, Irrational θ ∧ ∃ c : ℝ, c > 0 ∧
        ∀ k : ℕ, distInt (θ * seq k) ≥ c * ε^4 / log (1/ε) := by
  sorry

/-- Peres-Schlag: Improved bound -/
@[category research solved, AMS 11]
theorem erdos_464_peres_schlag :
    ∀ ε : ℝ, ε > 0 → ε < 1 → ∀ seq : ℕ → ℕ, StrictMono seq →
      (∀ k : ℕ, (seq (k + 1) : ℝ) ≥ (1 + ε) * seq k) →
      ∃ θ : ℝ, Irrational θ ∧ ∃ c : ℝ, c > 0 ∧
        ∀ k : ℕ, distInt (θ * seq k) ≥ c * ε / log (1/ε) := by
  sorry

end Erdos464
