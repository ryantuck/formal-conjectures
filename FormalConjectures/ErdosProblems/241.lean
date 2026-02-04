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
# Erdős Problem 241

*Reference:* [erdosproblems.com/241](https://www.erdosproblems.com/241)
-/

open Filter Topology Finset

namespace Erdos241

/--
All $r$-fold sums from a set are distinct (aside from trivial coincidences).
-/
def Has_r_fold_DistinctSums (r : ℕ) (A : Finset ℕ) : Prop :=
  ∀ S T : Finset ℕ, S ⊆ A → T ⊆ A → S.card = r → T.card = r →
    S.sum id = T.sum id → S = T

/--
Let $f(N)$ be the maximum size of $A\subseteq \{1,\ldots,N\}$ such that the sums
$a+b+c$ with $a,b,c\in A$ are all distinct (aside from the trivial coincidences).
Is it true that $f(N)\sim N^{1/3}$?

Originally asked to Erdős by Bose. Bose and Chowla [BoCh62] provided a construction
proving one half: $(1+o(1))N^{1/3}\leq f(N)$.
The best upper bound is due to Green [Gr01]: $f(N) \leq ((7/2)^{1/3}+o(1))N^{1/3}$.

[BoCh62] Bose, R. C. and Chowla, S., _Theorems in the additive theory of numbers_.
  Comment. Math. Helv. (1962), 141-147.

[Gr01] Green, B., _The Cameron-Erdős conjecture_.
  Bull. London Math. Soc. (2004), 769-778.
-/
@[category research open, AMS 11]
theorem erdos_241 : ∀ ε : ℝ, ε > 0 →
    ∃ C₁ C₂ : ℝ, C₁ > 0 ∧ C₂ > 0 ∧
    ∀ N : ℕ, N > 0 →
    let f := ⨆ (A : Finset ℕ) (h : A ⊆ Finset.range N ∧ Has_r_fold_DistinctSums 3 A), (A.card : ℝ);
    C₁ * (N : ℝ) ^ (1/3 - ε) ≤ f ∧ f ≤ C₂ * (N : ℝ) ^ (1/3 + ε) := by
  sorry

/--
Bose and Chowla's lower bound: $(1+o(1))N^{1/3}\leq f(N)$.
-/
@[category research solved, AMS 11]
theorem erdos_241.bose_chowla : ∃ o_fn : ℕ → ℝ, Tendsto o_fn atTop (𝓝 0) ∧
    ∀ N : ℕ, N > 0 →
    let f := ⨆ (A : Finset ℕ) (h : A ⊆ Finset.range N ∧ Has_r_fold_DistinctSums 3 A), (A.card : ℝ);
    f ≥ (1 + o_fn N) * (N : ℝ) ^ (1/3) := by
  sorry

/--
Green's upper bound: $f(N) \leq ((7/2)^{1/3}+o(1))N^{1/3}$.
-/
@[category research solved, AMS 11]
theorem erdos_241.green : ∃ o_fn : ℕ → ℝ, Tendsto o_fn atTop (𝓝 0) ∧
    ∀ N : ℕ, N > 0 →
    let f := ⨆ (A : Finset ℕ) (h : A ⊆ Finset.range N ∧ Has_r_fold_DistinctSums 3 A), (A.card : ℝ);
    f ≤ ((7/2 : ℝ) ^ (1/3) + o_fn N) * (N : ℝ) ^ (1/3) := by
  sorry

end Erdos241
