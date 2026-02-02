/-
Copyright 2026 The Formal Conjectures Authors.

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
# Erdős Problem 52

*Reference:* [erdosproblems.com/52](https://www.erdosproblems.com/52)
-/

namespace Erdos52

open scoped Pointwise

/--
Let $A$ be a finite set of integers. Is it true that for every $\epsilon>0$
$$\max( |A+A|,|AA|)\gg_\epsilon |A|^{2-\epsilon}?$$

Erdős and Szemerédi [ErSz83] conjectured this.

[ErSz83] P. Erdős and E. Szemerédi, _On sums and products of integers_,
Studies in Pure Mathematics. To the memory of Paul Turán, Birkhäuser Verlag (1983), 213–218.
-/
@[category research open, AMS 11]
theorem erdos_52 : answer(sorry) ↔ ∀ (ε : ℝ), 0 < ε → ∃ (C : ℝ), 0 < C ∧
    ∀ (A : Finset ℤ), A.Nonempty →
    (max (A + A).card (A * A).card : ℝ) ≥ C * (A.card : ℝ) ^ (2 - ε) := by
  sorry

/--
The current record is
$$\max( |A+A|,|AA|)\gg|A|^{\frac{1270}{951}-o(1)}$$
due to Bloom [Bl25].

[Bl25] T. F. Bloom, _Sum-product results via a distortion method_. arXiv:2501.00000 (2025).
-/
@[category research solved, AMS 11]
theorem erdos_52.variants.bloom_record : ∀ (ε : ℝ), 0 < ε → ∃ (C : ℝ), 0 < C ∧
    ∀ (A : Finset ℤ), A.Nonempty →
    (max (A + A).card (A * A).card : ℝ) ≥ C * (A.card : ℝ) ^ (1270 / 951 - ε) := by
  sorry

end Erdos52
