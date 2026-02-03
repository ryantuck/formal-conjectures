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
# Erdős Problem 116

*Reference:* [erdosproblems.com/116](https://www.erdosproblems.com/116)
-/

namespace Erdos116

open Polynomial MeasureTheory ENNReal

/--
Let $p(z) = \prod_{i=1}^n (z - z_i)$ with $|z_i| \le 1$.
The conjecture asks if the measure of the set $\{z \in \mathbb{C} : |p(z)| < 1\}$ is
at least $n^{-O(1)}$ or $(\log n)^{-O(1)}$.

[EHP58] Erdős, P. and Herzog, F. and Piranian, G., _Metric properties of polynomials_.
  J. Analyse Math. (1958), 125-148.
-/
@[category research solved, AMS 30]
theorem erdos_116 :
    ∃ (C k : ℝ), 0 < C ∧ ∀ (n : ℕ) (p : ℂ[X]),
      p.Monic → p.natDegree = n → n ≥ 1 →
      (∀ z ∈ p.rootSet ℂ, ‖z‖ ≤ 1) →
      volume {z | ‖p.eval z‖ < 1} ≥ ENNReal.ofReal (C * (n : ℝ) ^ (-k)) := by
  sorry

/--
Krishnapur, Lundberg, and Ramachandran [KLR25] proved that the measure is $\gg (\log n)^{-1}$.

[KLR25] Krishnapur, M., Lundberg, E., and Ramachandran, K., _The Erdős-Herzog-Piranian conjecture
on the measure of polynomial level sets_. arXiv:2501.03234 (2025).
-/
@[category research solved, AMS 30]
theorem erdos_116.strong :
    ∃ (C : ℝ), 0 < C ∧ ∀ (n : ℕ) (p : ℂ[X]),
      p.Monic → p.natDegree = n → n ≥ 2 →
      (∀ z ∈ p.rootSet ℂ, ‖z‖ ≤ 1) →
      volume {z | ‖p.eval z‖ < 1} ≥ ENNReal.ofReal (C / Real.log n) := by
  sorry

/--
Wagner [Wa88] proves, for $n\geq 3$, the existence of such polynomials with
$$ |\{ z: |p(z)| <1\}| \ll_\epsilon (\log\log n)^{-1/2+\epsilon} $$
for all $\epsilon > 0$.

[Wa88] Wagner, G., _On the measure of the level sets of harmonic polynomials_.
  Monatsh. Math. (1988), 69-81.
-/
@[category research solved, AMS 30]
theorem erdos_116.wagner (ε : ℝ) (hε : 0 < ε) :
    ∃ (C : ℝ), 0 < C ∧ ∀ (n : ℕ), n ≥ 3 →
      ∃ (p : ℂ[X]), p.Monic ∧ p.natDegree = n ∧
      (∀ z ∈ p.rootSet ℂ, ‖z‖ ≤ 1) ∧
      volume {z | ‖p.eval z‖ < 1} ≤ ENNReal.ofReal (C / (Real.log (Real.log n)) ^ (1 / 2 - ε)) := by
  sorry

end Erdos116
