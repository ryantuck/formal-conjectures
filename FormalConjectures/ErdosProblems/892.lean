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
# Erdős Problem 892

Primitive sequence with aₙ ≪ bₙ.

OPEN

*Reference:* [erdosproblems.com/892](https://www.erdosproblems.com/892)
-/

open Finset Nat Filter

open scoped Topology Real BigOperators

namespace Erdos892

/-- Primitive sequence: no term divides another -/
def IsPrimitive (a : ℕ → ℕ) : Prop :=
  ∀ i j : ℕ, i ≠ j → ¬(a i ∣ a j)

/-- Necessary condition (Erdős): ∑ 1/(bₙ log bₙ) < ∞ -/
@[category research solved, AMS 11]
theorem erdos_necessary_condition (b : ℕ → ℕ) (hb : ∀ n, b n < b (n + 1)) :
    (∃ a : ℕ → ℕ, IsPrimitive a ∧ ∃ C, ∀ n, a n ≤ C * b n) →
    ∃ M : ℝ, (∑' n : ℕ, (1 : ℝ) / (b n * Real.log (b n))) < M := by
  sorry

/-- Necessary condition (Erdős-Sárközy-Szemerédi): asymptotic bound on reciprocal sum -/
@[category research solved, AMS 11]
theorem ess_necessary_condition (b : ℕ → ℕ) (hb : ∀ n, b n < b (n + 1)) :
    (∃ a : ℕ → ℕ, IsPrimitive a ∧ ∃ C, ∀ n, a n ≤ C * b n) →
    ∀ᶠ x in atTop, (∑ n ∈ Finset.filter (fun n => b n < x) (Finset.range x), (1 : ℝ) / b n) <
      Real.log x / Real.sqrt (Real.log (Real.log x)) := by
  sorry

/-- Main question: necessary and sufficient condition -/
@[category research open, AMS 11]
theorem primitive_sequence_condition (answer : Prop) :
    answer ↔ ∃ (P : (ℕ → ℕ) → Prop),
      ∀ b : ℕ → ℕ, (∀ n, b n < b (n + 1)) →
        (P b ↔ ∃ a : ℕ → ℕ, IsPrimitive a ∧ ∃ C, ∀ n, a n ≤ C * b n) := by
  sorry

end Erdos892
