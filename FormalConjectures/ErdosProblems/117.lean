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
# Erdős Problem 117

*Reference:* [erdosproblems.com/117](https://www.erdosproblems.com/117)
-/

namespace Erdos117

open Group Subgroup

variable (G : Type*) [Group G]

/--
A set $S \subseteq G$ is pairwise non-commuting if for all distinct $x, y \in S$, $xy \neq yx$.
-/
def IsPairwiseNonCommuting (S : Set G) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x ≠ y → x * y ≠ y * x

/--
$G$ has the property that any subset of $> n$ elements contains a commuting pair.
Equivalently, every pairwise non-commuting finite set has cardinality at most $n$.
-/
def MaxNonCommutingSize (n : ℕ) : Prop :=
  ∀ A : Finset G, IsPairwiseNonCommuting G A → A.card ≤ n

/--
$G$ can be covered by at most $k$ Abelian subgroups.
-/
def CoveredByAbelianSubgroups (k : ℕ) : Prop :=
  ∃ (family : Finset (Subgroup G)), family.card ≤ k ∧
    (∀ H ∈ family, ∀ x ∈ H, ∀ y ∈ H, x * y = y * x) ∧
    (⋃ H ∈ family, (H : Set G)) = Set.univ

/--
Pyber [Py87] proved there exist constants $c_2 > c_1 > 1$ such that $c_1^n < h(n) < c_2^n$.
Here $h(n)$ is the minimal number such that any group satisfying the condition can be covered
by $h(n)$ abelian subgroups.
We formulate this as: there exists a function $h(n)$ satisfying the covering property for all groups,
and this function is bounded.

[Py87] Pyber, L., _On the number of abelian subgroups of a finite group_.
  Period. Math. Hungar. (1987), 69-82.
-/
@[category research solved, AMS 20]
theorem erdos_117 :
    ∃ c₁ c₂ : ℝ, 1 < c₁ ∧ c₁ < c₂ ∧
      ∃ h : ℕ → ℕ,
        (∀ n, ∀ (G : Type) [Group G], MaxNonCommutingSize G n → CoveredByAbelianSubgroups G (h n)) ∧
        (∀ n ≥ 1, (c₁ ^ n : ℝ) < h n ∧ (h n : ℝ) < c₂ ^ n) := by
  sorry

end Erdos117
