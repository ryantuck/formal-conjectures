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
# Erdős Problem 682

For almost all n, does there exist m ∈ (p_n, p_{n+1}) such that p(m) ≥ p_{n+1} - p_n,
where p(m) denotes the least prime factor of m?

PROVED by Gafni and Tao

*Reference:* [erdosproblems.com/682](https://www.erdosproblems.com/682)
-/

open Nat

open scoped Topology Real

namespace Erdos682

/-- p(m): least prime factor of m -/
noncomputable def leastPrimeFactor (m : ℕ) : ℕ := sorry

/-- nth prime -/
noncomputable def nthPrime (n : ℕ) : ℕ := sorry

/-- For almost all n, ∃m ∈ (p_n, p_{n+1}) with p(m) ≥ p_{n+1} - p_n -/
@[category research solved, AMS 11]
theorem prime_gap_least_prime_factor :
    ∀ ε > 0, Filter.Tendsto
      (fun X => ((Finset.range X).filter (fun n => sorry)).card / X)
      Filter.atTop (nhds 1) := by
  sorry

end Erdos682
