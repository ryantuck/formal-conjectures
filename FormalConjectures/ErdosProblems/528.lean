/-
Copyright 2025 The Formal Conjectures Authors.

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
# Erdős Problem 528

Let f(n,k) be the number of self-avoiding walks with n steps in ℤ^k.
Determine the connective constant C_k = lim_{n→∞} f(n,k)^{1/n}.

OPEN. Known: k ≤ C_k ≤ 2k-1, and C_k = 2k-1-1/(2k)+O(1/k²).

*Reference:* [erdosproblems.com/528](https://www.erdosproblems.com/528)
-/

open Filter Real Topology

namespace Erdos528

/-- Number of self-avoiding walks in k dimensions -/
noncomputable def selfAvoidingWalks (n k : ℕ) : ℕ := sorry

/-- The connective constant for self-avoiding walks -/
@[category research open, AMS 82]
theorem connective_constant_exists (k : ℕ) (hk : k > 0) :
    ∃ C : ℝ, C > 0 ∧
      Tendsto (fun n => (selfAvoidingWalks n k : ℝ) ^ (1 / (n : ℝ))) atTop (𝓝 C) ∧
      (k : ℝ) ≤ C ∧ C ≤ 2 * k - 1 := by
  sorry

end Erdos528
