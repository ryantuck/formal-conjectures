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
# Erdős Problem 305

For integers $1 \leq a < b$, let $D(a,b)$ denote the minimal value of $n_k$ such that
there exist integers $1 \leq n_1 < \cdots < n_k$ with $\frac{a}{b} = \frac{1}{n_1} + \cdots + \frac{1}{n_k}$.

Estimate $D(b) = \max_{1 \leq a < b} D(a,b)$. Is it true that $D(b) \ll b(\log b)^{1+o(1)}$?

Bleicher and Erdős: $D(b) \ll b(\log b)^2$.
Yokota (1988): $D(b) \ll b(\log b)(\log \log b)^4(\log \log \log b)^2$.
Liu and Sawhney (2024): $D(b) \ll b(\log b)(\log \log b)^3(\log \log \log b)^{O(1)}$.

*Reference:* [erdosproblems.com/305](https://www.erdosproblems.com/305)
-/

open Filter Topology BigOperators

namespace Erdos305

/-- A representation of a rational as a sum of distinct unit fractions -/
def UnitFractionRep (a b : ℕ) (ns : List ℕ) : Prop :=
  ns.Sorted (· < ·) ∧
  (∀ n ∈ ns, n > 0) ∧
  (a : ℚ) / b = (ns.map (fun n => (1 : ℚ) / n)).sum

/-- D(a,b) is the minimal largest denominator in a unit fraction representation of a/b -/
noncomputable def D_ab (a b : ℕ) : ℕ :=
  sInf {k : ℕ | ∃ ns : List ℕ, UnitFractionRep a b ns ∧ ns ≠ [] ∧ ns.getLast? = some k}

/-- D(b) is the maximum of D(a,b) over all 1 ≤ a < b -/
noncomputable def D (b : ℕ) : ℕ :=
  sSup (Set.image (fun a => D_ab a b) {a : ℕ | 0 < a ∧ a < b})

/-- Bleicher-Erdős: D(b) is O(b(log b)²) -/
@[category research solved, AMS 11]
theorem erdos_305_bleicher_erdos :
    ∃ C : ℝ, ∀ b : ℕ, b > 0 →
      (D b : ℝ) ≤ C * b * (Real.log b) ^ 2 := by
  sorry

/-- Yokota (1988): Improved bound for D(b) -/
@[category research solved, AMS 11]
theorem erdos_305_yokota :
    ∃ C : ℝ, ∀ b : ℕ, b > 2 →
      (D b : ℝ) ≤ C * b * Real.log b * (Real.log (Real.log b)) ^ 4 *
        (Real.log (Real.log (Real.log b))) ^ 2 := by
  sorry

/-- Liu-Sawhney (2024): Further improved bound -/
@[category research solved, AMS 11]
theorem erdos_305_liu_sawhney :
    ∃ C : ℝ, ∀ b : ℕ, b > 2 →
      (D b : ℝ) ≤ C * b * Real.log b * (Real.log (Real.log b)) ^ 3 := by
  sorry

/-- Lower bound for primes: D(p) is Ω(p log p) -/
@[category research solved, AMS 11]
theorem erdos_305_lower_bound_primes :
    ∃ c : ℝ, c > 0 ∧ ∃ᶠ p in atTop, p.Prime ∧ (D p : ℝ) ≥ c * p * Real.log p := by
  sorry

end Erdos305
