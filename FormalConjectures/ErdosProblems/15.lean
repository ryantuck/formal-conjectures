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
# Erdős Problem 15

*Reference:* [erdosproblems.com/15](https://www.erdosproblems.com/15)
-/

open Real

namespace Erdos15

/--
Is it true that
$$ \sum_{n=1}^\infty (-1)^n \frac{n}{p_n} $$
converges, where $p_n$ is the $n$-th prime?

Tao [Ta23] has proved that this series does converge assuming a strong form of the
Hardy-Littlewood prime tuples conjecture.

[Ta23] Tao, T., _The Erdős alternating series conjecture_. arXiv:2308.16335 (2023).
-/
@[category research open, AMS 11]
theorem erdos_15 : answer(sorry) ↔ Summable (fun n : ℕ ↦ (-1 : ℝ) ^ n * (n : ℝ) / (n.nth Nat.Prime : ℝ)) := by
  sorry

/--
Erdős conjectured that
$$ \sum_{n=1}^\infty (-1)^n \frac{1}{n(p_{n+1}-p_n)} $$
converges.
-/
@[category research open, AMS 11]
theorem erdos_15.variants.gaps_converge :
    Summable (fun n : ℕ ↦ (-1 : ℝ) ^ n / ((n + 1 : ℝ) * ((n + 1).nth Nat.Prime - n.nth Nat.Prime : ℝ))) := by
  sorry

/--
Erdős conjectured that
$$ \sum_{n=1}^\infty (-1)^n \frac{1}{p_{n+1}-p_n} $$
diverges.

Existence of infinitely many bounded gaps between primes (Zhang [Zh14]) implies this series
does not converge.

[Zh14] Zhang, Y., _Bounded gaps between primes_. Annals of Mathematics (2014), 1121-1174.
-/
@[category research solved, AMS 11]
theorem erdos_15.variants.gaps_diverge :
    ¬ Summable (fun n : ℕ ↦ (-1 : ℝ) ^ n / ((n + 1).nth Nat.Prime - n.nth Nat.Prime : ℝ)) := by
  sorry

end Erdos15
