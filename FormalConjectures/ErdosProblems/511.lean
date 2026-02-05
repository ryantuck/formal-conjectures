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
# Erdős Problem 511

For a monic polynomial f(z) ∈ ℂ[z] of degree n, determine whether for every c > 1,
the set {z ∈ ℂ : |f(z)| < 1} has at most O_c(1) connected components with diameter
greater than c (with the implied constant independent of n).

DISPROVED: Pommerenke and Huang showed that for any 0 < d < 4 and k ≥ 1, there exist
monic polynomials such that {z : |f(z)| ≤ 1} has at least k components with diameter ≥ d.

However, Pólya proved no component can have diameter exceeding 4.

*Reference:* [erdosproblems.com/511](https://www.erdosproblems.com/511)
-/

open Filter Topology Metric

namespace Erdos511

/-- The Erdős conjecture on polynomial level sets is false -/
@[category research solved, AMS 30]
theorem erdos_511_disproved :
    ¬∀ (c : ℝ), c > 1 →
      ∃ K : ℕ, ∀ (n : ℕ) (f : Polynomial ℂ), f.Monic → f.natDegree = n →
        ∃ (Components : Set (Set ℂ)),
          (∀ C ∈ Components, IsConnected C ∧ C ⊆ {z : ℂ | ‖f.eval z‖ < 1}) ∧
          (∀ z ∈ {z : ℂ | ‖f.eval z‖ < 1}, ∃ C ∈ Components, z ∈ C) ∧
          (∀ C₁ C₂, C₁ ∈ Components → C₂ ∈ Components → C₁ ≠ C₂ → Disjoint C₁ C₂) ∧
          Nat.card {C ∈ Components | diam C > c} ≤ K := by
  sorry

/-- Pólya's bound: no component has diameter exceeding 4 -/
@[category research solved, AMS 30]
theorem polya_diameter_bound (f : Polynomial ℂ) (hf : f.Monic) :
    ∀ (Components : Set (Set ℂ)),
      (∀ C ∈ Components, IsConnected C ∧ C ⊆ {z : ℂ | ‖f.eval z‖ < 1}) →
      (∀ z ∈ {z : ℂ | ‖f.eval z‖ < 1}, ∃ C ∈ Components, z ∈ C) →
      (∀ C₁ C₂, C₁ ∈ Components → C₂ ∈ Components → C₁ ≠ C₂ → Disjoint C₁ C₂) →
      ∀ C ∈ Components, diam C ≤ 4 := by
  sorry

end Erdos511
