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
# Erdős Problem 1141

Infinitely many n with property that n-k² is prime for coprime k with k²<n.

This problem asks whether there exist infinitely many natural numbers n such that
for every k coprime to n with k² < n, the difference n - k² is prime.

This is related to Problem 1140 but requires coprimality between k and n,
which significantly changes the problem's character.

OPEN

*Reference:* [erdosproblems.com/1141](https://www.erdosproblems.com/1141)
-/

namespace Erdos1141

/-- There are infinitely many natural numbers n such that n-k² is prime for all k
    coprime to n with k² < n. This is an open problem. -/
@[category research open, AMS 11]
theorem infinitely_many_n_prime_shift :
    Set.Infinite {n : ℕ | ∀ k : ℕ, k^2 < n → Nat.Coprime k n →
      (n - k^2).Prime} := by
  sorry

end Erdos1141
