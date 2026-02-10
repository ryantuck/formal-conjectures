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
# Erdős Problem 902

Tournament domination.

OPEN

*Reference:* [erdosproblems.com/902](https://www.erdosproblems.com/902)
-/

open Finset

open scoped Topology Real

namespace Erdos902

variable {α : Type*}

/-- Tournament: complete directed graph -/
def IsTournament (T : α → α → Prop) : Prop :=
  ∀ x y : α, x ≠ y → (T x y ∨ T y x) ∧ ¬(T x y ∧ T y x)

/-- Vertex v dominates set S in tournament -/
def Dominates (T : α → α → Prop) (v : α) (S : Finset α) : Prop :=
  ∀ s ∈ S, T v s

/-- f(n): minimal vertices such that every n vertices dominated by one other -/
noncomputable def f (n : ℕ) : ℕ :=
  sInf {m : ℕ | ∃ (α : Type) (_ : Fintype α) (T : α → α → Prop),
    IsTournament T ∧ Fintype.card α = m ∧
    ∀ S : Finset α, S.card = n → ∃ v : α, v ∉ S ∧ Dominates T v S}

/-- Base cases: f(1) = 3, f(2) = 7 -/
@[category research solved, AMS 5]
theorem base_cases : f 1 = 3 ∧ f 2 = 7 := by
  sorry

/-- Erdős bounds: 2^(n+1) - 1 ≤ f(n) ≪ n²2ⁿ -/
@[category research solved, AMS 5]
theorem erdos_bounds (n : ℕ) (hn : n ≥ 1) :
    2 ^ (n + 1) - 1 ≤ f n ∧
    ∃ C : ℝ, C > 0 ∧ (f n : ℝ) ≤ C * (n : ℝ) ^ 2 * (2 : ℝ) ^ n := by
  sorry

/-- Szekeres-Szekeres: f(3) = 19 and n2ⁿ ≪ f(n) -/
@[category research solved, AMS 5]
theorem szekeres_result :
    f 3 = 19 ∧
    ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n ≥ 1 →
      C * n * (2 : ℝ) ^ n ≤ (f n : ℝ) := by
  sorry

/-- Main question: estimate f(n) -/
@[category research open, AMS 5]
theorem tournament_domination :
    ∃ g : ℕ → ℝ, ∀ ε > 0, ∃ n₀ : ℕ, ∀ n ≥ n₀,
      (1 - ε) * g n ≤ (f n : ℝ) ∧ (f n : ℝ) ≤ (1 + ε) * g n := by
  sorry

end Erdos902
