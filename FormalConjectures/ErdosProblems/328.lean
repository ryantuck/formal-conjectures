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
# Erdős Problem 328

Given a set $A \subseteq \mathbb{N}$ and constant $C > 0$ such that the representation
function $1_A \ast 1_A(n) \leq C$ for all $n$, can $A$ be partitioned into $t$ subsets
(where $t$ depends only on $C$) such that each subset has representation function < C?

Nešetřil and Rödl proved the answer is NO for all C.

*Reference:* [erdosproblems.com/328](https://www.erdosproblems.com/328)
-/

open Filter Topology BigOperators

namespace Erdos328

/-- Representation function: count of ways to write n as a+b with a,b ∈ A -/
noncomputable def rep (A : Set ℕ) (n : ℕ) : ℕ :=
  Nat.card {p : ℕ × ℕ | p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n}

/-- Nešetřil-Rödl: No bounded partition exists -/
@[category research solved, AMS 11]
theorem erdos_328_disproved :
    ∀ C : ℕ, C > 0 → ¬∃ t : ℕ, ∀ A : Set ℕ,
      (∀ n, rep A n ≤ C) →
      ∃ partition : Fin t → Set ℕ,
        (∀ i, partition i ⊆ A) ∧
        (∀ i j, i ≠ j → Disjoint (partition i) (partition j)) ∧
        (⋃ i, partition i = A) ∧
        (∀ i n, rep (partition i) n < C) := by
  sorry

end Erdos328
