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
# Erdős Problem 646

Are there infinitely many n where n! is divisible by an even power of each prime p_i?

PROVED by Berend (1997)

*Reference:* [erdosproblems.com/646](https://www.erdosproblems.com/646)
-/

open Nat

open scoped Topology Real

namespace Erdos646

/-- Infinitely many n where n! is divisible by even power of each prime -/
@[category research solved, AMS 11]
theorem factorial_even_prime_powers :
    ∀ M : ℕ, ∃ n > M, ∀ p : ℕ, p.Prime →
      ∃ k : ℕ, (p ^ (2*k)) ∣ factorial n := by
  sorry

end Erdos646
