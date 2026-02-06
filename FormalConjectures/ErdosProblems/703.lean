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
# Erdős Problem 703

Estimate T(n,r) - max family size where no A,B have |A∩B|=r.

PROVED by Frankl and Rödl (1987); optimal bounds by Frankl and Füredi ($250 reward)

*Reference:* [erdosproblems.com/703](https://www.erdosproblems.com/703)
-/

open Finset Nat

open scoped Topology Real

namespace Erdos703

/-- T(n,r): max size of family with no intersection of size exactly r -/
noncomputable def T (n r : ℕ) : ℕ := sorry

/-- Optimal bounds for T(n,r) -/
@[category research solved, AMS 05]
theorem max_family_no_intersection_size_r (r : ℕ) :
    ∃ f : ℕ → ℕ, ∀ n : ℕ, T n r ~ f n := by
  sorry

end Erdos703
