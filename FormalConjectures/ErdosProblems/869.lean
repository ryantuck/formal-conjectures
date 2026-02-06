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
# Erdős Problem 869

Union of disjoint bases contains minimal basis.

OPEN

*Reference:* [erdosproblems.com/869](https://www.erdosproblems.com/869)
-/

open Finset

open scoped Topology Real

namespace Erdos869

/-- Additive basis of order 2 -/
def IsAdditiveBasis2 (A : Set ℕ) : Prop := sorry

/-- Minimal additive basis -/
def IsMinimalAdditiveBasis2 (A : Set ℕ) : Prop := sorry

/-- Union of disjoint bases contains minimal basis -/
@[category research open, AMS 11]
theorem disjoint_bases_minimal (answer : Prop) :
    answer ↔ ∀ (A₁ A₂ : Set ℕ),
      Disjoint A₁ A₂ →
      IsAdditiveBasis2 A₁ →
      IsAdditiveBasis2 A₂ →
      ∃ (B : Set ℕ), B ⊆ A₁ ∪ A₂ ∧ IsMinimalAdditiveBasis2 B := by
  sorry

end Erdos869
