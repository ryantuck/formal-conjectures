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
# Erdős Problem 334

Find the optimal function $f(n)$ such that every positive integer $n$ can be expressed as
$n = a + b$, where both $a$ and $b$ are $f(n)$-smooth (not divisible by any prime > f(n)).

Erd ős asked if $f(n) \leq n^{1/3}$. Balog proved $f(n) \ll_\epsilon n^{4/(9\sqrt{e})+\epsilon}$.
It is conjectured that $f(n) \leq n^{o(1)}$ or even $f(n) \leq e^{O(\sqrt{\log n})}$.

*Reference:* [erdosproblems.com/334](https://www.erdosproblems.com/334)
-/

open Filter Topology BigOperators Real

namespace Erdos334

/-- A number is B-smooth if all its prime factors are at most B -/
def IsSmooth (n B : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → p ≤ B

/-- The minimal smoothness bound for decomposing n as sum of two smooth numbers -/
noncomputable def f (n : ℕ) : ℕ :=
  sInf {B : ℕ | ∃ a b : ℕ, a + b = n ∧ IsSmooth a B ∧ IsSmooth b B}

/-- Erdős's question: Is f(n) ≤ n^(1/3)? -/
@[category research solved, AMS 11]
theorem erdos_334_cube_root :
    ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n > 0 → (f n : ℝ) ≤ C * (n : ℝ) ^ ((1:ℝ)/3) := by
  sorry

/-- Balog's bound: f(n) ≪_ε n^(4/(9√e)+ε) -/
@[category research open, AMS 11]
theorem erdos_334_balog :
    ∀ ε > 0, ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n > 1 →
      (f n : ℝ) ≤ C * (n : ℝ) ^ (4 / (9 * Real.sqrt (exp 1)) + ε) := by
  sorry

/-- Conjecture: f(n) = n^(o(1)) -/
def erdos_334_conjecture_polylog : Prop :=
  ∀ ε > 0, ∀ᶠ n : ℕ in atTop, (f n : ℝ) ≤ (n : ℝ) ^ ε

/-- Stronger conjecture: f(n) ≤ exp(O(√(log n))) -/
def erdos_334_conjecture_exp_sqrt_log : Prop :=
  ∃ C : ℝ, C > 0 ∧ ∀ᶠ n : ℕ in atTop,
    (f n : ℝ) ≤ exp (C * Real.sqrt (log (n : ℝ)))

end Erdos334
