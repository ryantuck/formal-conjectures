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
# Erdős Problem 702

If k-uniform family with |F| > C(n-2,k-2), do ∃ A,B with |A∩B|=1?

PROVED

*Reference:* [erdosproblems.com/702](https://www.erdosproblems.com/702)
-/

open Finset Nat

open scoped Topology Real

namespace Erdos702

/-- Large k-uniform family has sets with intersection size 1 -/
@[category research solved, AMS 05]
theorem large_uniform_family_intersection_one (n k : ℕ) :
    ∀ (F : Finset (Finset (Fin n))),
      (∀ A ∈ F, A.card = k) →
      F.card > Nat.choose (n-2) (k-2) →
      ∃ A B, A ∈ F ∧ B ∈ F ∧ A ≠ B ∧ (A ∩ B).card = 1 := by
  sorry

end Erdos702
