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
# Erdős Problem 903

Block designs on n=p²+p+1.

PROVED

*Reference:* [erdosproblems.com/903](https://www.erdosproblems.com/903)
-/

open Finset Nat

open scoped Topology Real

namespace Erdos903

/-- Block design bound -/
@[category research solved, AMS 05]
theorem block_design_prime_bound (p : ℕ) (hp : p.Prime) :
    ∀ (t : ℕ), let n := p ^ 2 + p + 1
      t > n → t ≥ n + p := by
  sorry

end Erdos903
