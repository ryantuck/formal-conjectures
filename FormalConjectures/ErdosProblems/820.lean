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
# Erdős Problem 820

H(n) for coprime exponentials.

OPEN

*Reference:* [erdosproblems.com/820](https://www.erdosproblems.com/820)
-/

open Finset Nat

open scoped Topology Real

namespace Erdos820

/-- H(n): smallest l where ∃k<l with gcd(k^n-1,l^n-1)=1 -/
noncomputable def H (n : ℕ) : ℕ := sorry

/-- Questions on growth and behavior of H(n) -/
@[category research open, AMS 11]
theorem coprime_exponentials :
    sorry := by
  sorry

end Erdos820
