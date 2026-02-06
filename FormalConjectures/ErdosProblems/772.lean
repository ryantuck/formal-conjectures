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
# Erdős Problem 772

Sidon subset in bounded convolution sets.

PROVED

*Reference:* [erdosproblems.com/772](https://www.erdosproblems.com/772)
-/

open Finset

open scoped Topology Real

namespace Erdos772

/-- H_k(n): maximum Sidon subset size -/
noncomputable def H_k (k n : ℕ) : ℕ := sorry

/-- H_k(n) ≫_k n^(2/3) -/
@[category research solved, AMS 11]
theorem sidon_bounded_convolution (k : ℕ) :
    ∃ c : ℝ, c > 0 ∧
      ∀ᶠ (n : ℕ) in Filter.atTop,
        H_k k n ≥ c * (n : ℝ) ^ (2/3 : ℝ) := by
  sorry

end Erdos772
