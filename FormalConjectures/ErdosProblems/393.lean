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
# Erdős Problem 393

Let $f(n)$ be the minimal $m \geq 1$ such that $n! = a_1 \cdots a_t$ where
$a_1 < \cdots < a_t = a_1 + m$.

What is the behavior of f(n)? Is f(n) = 1 infinitely often?

Berend-Osgood: $F_m(N) = o(N)$ for each fixed m.
Bui-Pratt-Zaharescu: $F_m(N) \ll_m N^{33/34}$.
Luca: Assuming ABC, f(n) → ∞.

*Reference:* [erdosproblems.com/393](https://www.erdosproblems.com/393)
-/

open Filter Topology BigOperators Real

namespace Erdos393

/-- f(n) is the minimal span of factorization as consecutive-valued product -/
noncomputable def f (n : ℕ) : ℕ :=
  sInf {m : ℕ | m ≥ 1 ∧ ∃ t a₁ : ℕ, ∃ seq : Finset ℕ,
    seq.card = t ∧ (∀ i < t, a₁ + i ∈ seq) ∧ seq.prod id = n.factorial ∧
    seq.max' (by sorry) = a₁ + m}

/-- Count of n ≤ N with f(n) = m -/
noncomputable def F (m N : ℕ) : ℕ :=
  Nat.card {n : ℕ | n ≤ N ∧ f n = m}

/-- Berend-Osgood: F_m(N) = o(N) -/
@[category research open, AMS 11]
theorem erdos_393_berend_osgood :
    ∀ m : ℕ, ∀ ε > 0, ∀ᶠ N : ℕ in atTop, (F m N : ℝ) < ε * N := by
  sorry

/-- Bui-Pratt-Zaharescu: Improved bound -/
@[category research open, AMS 11]
theorem erdos_393_bui_pratt_zaharescu :
    ∀ m : ℕ, ∃ C : ℝ, C > 0 ∧ ∀ N : ℕ, (F m N : ℝ) ≤ C * (N : ℝ) ^ ((33:ℝ)/34) := by
  sorry

end Erdos393
