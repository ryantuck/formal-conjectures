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
# Erdős Problem 270

*Reference:* [erdosproblems.com/270](https://www.erdosproblems.com/270)
-/

open Filter Topology

namespace Erdos270

/--
For a function $f(n) \to \infty$ as $n \to \infty$, is the sum
$$\sum_{n\geq 1} \frac{1}{(n+1)\cdots (n+f(n))}$$
necessarily irrational?

This was disproved by Crmarić and Kovač (2025), who showed that for any $\alpha \in (0,\infty)$,
there exists $f:\mathbb{N}\to\mathbb{N}$ with $f(n)\to\infty$ such that the sum equals $\alpha$.
-/
@[category research solved, AMS 11]
theorem erdos_270 : ¬ ∀ f : ℕ → ℕ, Tendsto f atTop atTop →
    Irrational (∑' n : ℕ, (1 : ℝ) / ∏ k : Fin (f n), ((n + 1 + k.val : ℕ) : ℝ)) := by
  sorry

/--
Crmarić and Kovač (2025): For any $\alpha \in (0,\infty)$, there exists $f:\mathbb{N}\to\mathbb{N}$
with $f(n)\to\infty$ such that the sum equals $\alpha$.
-/
@[category research solved, AMS 11]
theorem erdos_270.crmovic_kovac (α : ℝ) (hα : α > 0) :
    ∃ f : ℕ → ℕ, Tendsto f atTop atTop ∧
      (∑' n : ℕ, (1 : ℝ) / ∏ k : Fin (f n), ((n + 1 + k.val : ℕ) : ℝ)) = α := by
  sorry

/--
Hansen (1975): The sum $\sum_n \frac{1}{\binom{2n}{n}} = \frac{1}{3}+\frac{2\pi}{3^{5/2}}$
is transcendental. This corresponds to $f(n) = n$.
-/
@[category research solved, AMS 11]
theorem erdos_270.hansen :
    (∑' n : ℕ, (1 : ℝ) / Nat.choose (2 * n) n) = 1/3 + 2 * Real.pi / 3^(5/2 : ℝ) ∧
    Transcendental ℚ (∑' n : ℕ, (1 : ℝ) / Nat.choose (2 * n) n) := by
  sorry

/--
Crmarić and Kovač (2025): If $f$ is required to be nondecreasing,
the set of possible values has Lebesgue measure zero.
-/
@[category research solved, AMS 11]
theorem erdos_270.nondecreasing_measure_zero :
    MeasureTheory.volume {α : ℝ | ∃ f : ℕ → ℕ, Monotone f ∧ Tendsto f atTop atTop ∧
      (∑' n : ℕ, (1 : ℝ) / ∏ k : Fin (f n), ((n + 1 + k.val : ℕ) : ℝ)) = α} = 0 := by
  sorry

end Erdos270
