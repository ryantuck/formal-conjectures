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
# Erdős Problem 232

*Reference:* [erdosproblems.com/232](https://www.erdosproblems.com/232)
-/

open MeasureTheory Metric Filter Topology

namespace Erdos232

/--
For $A\subset \mathbb{R}^2$ we define the upper density as
$\overline{\delta}(A)=\limsup_{R\to \infty}\frac{\lambda(A \cap B_R)}{\lambda(B_R)}$,
where $\lambda$ is the Lebesgue measure and $B_R$ is the ball of radius $R$.
-/
noncomputable def upperDensity (A : Set (ℝ × ℝ)) : ℝ :=
  limsup (fun R : ℝ => (volume (A ∩ closedBall (0, 0) R)).toReal / (volume (closedBall (0, 0) R : Set (ℝ × ℝ))).toReal) atTop

/--
$m_1$ is the supremum of upper densities over all measurable subsets of $\mathbb{R}^2$
without two points distance $1$ apart.
-/
noncomputable def m_1 : ℝ :=
  ⨆ (A : Set (ℝ × ℝ)) (h : MeasurableSet A ∧ ∀ x y, x ∈ A → y ∈ A → x ≠ y → dist x y ≠ 1), upperDensity A

/--
Estimate $m_1$. In particular, is $m_1\leq 1/4$?

A question of Moser [Mo66]. The answer is yes - Ambrus, Csiszárik, Matolcsi, Varga,
and Zsámboki [ACMVZ23] proved that $m_1\leq 0.247$.

[Mo66] Moser, L., _Problem 65-12. Points at rational distance in Euclidean space_.
  SIAM Review (1966), 246.

[ACMVZ23] Ambrus, G., Csiszárik, A., Matolcsi, M., Varga, N. and Zsámboki, S.,
  _On the density of sets avoiding parallelohedron distance 1_.
  arXiv:2307.00191 (2023).
-/
@[category research solved, AMS 52]
theorem erdos_232 : m_1 ≤ 1 / 4 := by
  sorry

/--
Ambrus et al. proved the stronger result $m_1 \leq 0.247$.
-/
@[category research solved, AMS 52]
theorem erdos_232.sharp : m_1 ≤ 0.247 := by
  sorry

end Erdos232
