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
# Erdős Problem 5

*Reference:* [erdosproblems.com/5](https://www.erdosproblems.com/5)
-/

namespace Erdos5

/--
De Polignac's conjecture: For every positive even integer $2k$, there are infinitely many
consecutive primes $p_n, p_{n+1}$ such that $p_{n+1} - p_n = 2k$.

Note: This formalization assumes Problem 5 refers to Polignac's conjecture given its relation
to prime gaps (OEIS A001223).
-/
@[category research open, AMS 11]
theorem erdos_5 : ∀ k > 0, {n | primeGap n = 2 * k}.Infinite := by
  sorry

/--
The Twin Prime Conjecture: There are infinitely many twin primes.
-/
@[category research open, AMS 11]
theorem erdos_5.variants.twin_prime : {n | primeGap n = 2}.Infinite := by
  sorry

end Erdos5
