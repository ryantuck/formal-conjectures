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
# Erdős Problem 656

Let A ⊂ ℕ have positive upper density. Must there exist an infinite set B and integer t
such that B+B+t ⊆ A?

SOLVED by Kra, Moreira, Richter, and Robertson (2024)

*Reference:* [erdosproblems.com/656](https://www.erdosproblems.com/656)
-/

open scoped Topology Real

namespace Erdos656

/-- Upper density of a set -/
noncomputable def upperDensity (A : Set ℕ) : ℝ := sorry

/-- Positive upper density implies B+B+t ⊆ A for some infinite B and t -/
@[category research solved, AMS 11]
theorem upper_density_sumset (A : Set ℕ) (h : upperDensity A > 0) :
    ∃ (B : Set ℕ) (t : ℤ), B.Infinite ∧
      ∀ b₁ b₂, b₁ ∈ B → b₂ ∈ B → (b₁ + b₂ + t : ℤ) ∈ (A.image (·:ℕ→ℤ)) := by
  sorry

end Erdos656
