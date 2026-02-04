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
# Erdős Problem 222

*Reference:* [erdosproblems.com/222](https://www.erdosproblems.com/222)
-/

open Filter

namespace Erdos222

/--
A natural number is a sum of two squares if there exist $x, y \in \mathbb{N}$
such that $n = x^2 + y^2$.
-/
def IsSumOfTwoSquares (n : ℕ) : Prop :=
  ∃ x y : ℕ, n = x^2 + y^2

/--
The set of integers which are the sum of two squares.
-/
def S : Set ℕ := { n | IsSumOfTwoSquares n }

/--
The sequence $n_1 < n_2 < \dots$ of integers which are the sum of two squares.
-/
noncomputable def n_ : ℕ → ℕ
  | 0 => sInf S
  | k + 1 => sInf { n ∈ S | n > n_ k }

/--
Explore the behaviour of the consecutive differences $n_{k+1} - n_k$.
-/
@[category research open, AMS 11]
theorem erdos_222 : ∃ C > 0, ∀ᶠ k in atTop, n_ (k + 1) - n_ k < C * (n_ k : ℝ)^(1/4) := by
  sorry

/--
Erdős [Er51] proved that, for infinitely many $k$,
$$ n_{k+1}-n_k \gg \frac{\log n_k}{\sqrt{\log\log n_k}}. $$

[Er51] Erdős, P., _On the sum of two squares_.
  J. London Math. Soc. (1951), 244-247.
-/
@[category research solved, AMS 11]
theorem erdos_222.lb : ∃ C > 0, ∃ᶠ k in atTop,
    (n_ (k + 1) - n_ k : ℝ) > C * Real.log (n_ k) / Real.sqrt (Real.log (Real.log (n_ k))) := by
  sorry

/--
Richards [Ri82] improved this to
$$ \limsup_{k	o \infty} \frac{n_{k+1}-n_k}{\log n_k} \geq 1/4. $$

[Ri82] Richards, I., _On the gaps between numbers which are sums of two squares_.
  Adv. in Math. (1982), 1-2.
-/
@[category research solved, AMS 11]
theorem erdos_222.richards_lb :
    limsup (fun k ↦ (n_ (k + 1) - n_ k : ℝ) / Real.log (n_ k)) atTop ≥ 1 / 4 := by
  sorry

/--
Bambah and Chowla [BaCh47] proved that
$$ n_{k+1}-n_k \ll n_k^{1/4}. $$

[BaCh47] Bambah, R. P. and Chowla, S., _On the difference between consecutive sums of two squares_.
  Proc. Nat. Inst. Sci. India (1947), 101-103.
-/
@[category research solved, AMS 11]
theorem erdos_222.ub : ∃ C > 0, ∀ k, (n_ (k + 1) - n_ k : ℝ) ≤ C * (n_ k : ℝ)^(1 / 4) := by
  sorry

end Erdos222
