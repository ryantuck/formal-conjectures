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
# Erdős Problem 432

Let A, B ⊆ ℕ be two infinite sets. How dense can A+B be if all elements of A+B are
pairwise relatively prime?

Problem proposed by Straus, inspired by Ostmann's Problem 431.

*Reference:* [erdosproblems.com/432](https://www.erdosproblems.com/432)
-/

open Filter Topology BigOperators

namespace Erdos432

/-- Erdős-Straus: Maximum density of sum set with coprime elements -/
@[category research open, AMS 11]
theorem erdos_432 :
    ∃ α : ℝ, 0 < α ∧ α = sSup {d : ℝ | ∃ A B : Set ℕ, A.Infinite ∧ B.Infinite ∧
      (∀ x y : ℕ, (∃ a ∈ A, ∃ b ∈ B, x = a + b) →
        (∃ a ∈ A, ∃ b ∈ B, y = a + b) → x ≠ y → Nat.Coprime x y) ∧
      limsup (fun n : ℕ =>
        (Nat.card {s : ℕ | s ≤ n ∧ ∃ a ∈ A, ∃ b ∈ B, s = a + b} : ℝ) / n) atTop = d} := by
  sorry

end Erdos432
