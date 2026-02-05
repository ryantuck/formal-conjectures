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
# Erdős Problem 514

Let f(z) be an entire transcendental function. Does there exist a path L such that
for every n, |f(z)/z^n| → ∞ as z → ∞ along L?

OPEN with partial results by Boas.

*Reference:* [erdosproblems.com/514](https://www.erdosproblems.com/514)
-/

open Topology Filter Complex

namespace Erdos514

/-- For entire transcendental functions, paths with super-polynomial growth exist -/
@[category research open, AMS 30]
theorem growth_path_conjecture :
    ∀ (f : ℂ → ℂ), Differentiable ℂ f →
      (∀ (p : Polynomial ℂ), ∃ z : ℂ, f z ≠ p.eval z) →
      ∃ (L : ℝ → ℂ), Continuous L ∧ Tendsto (‖L ·‖) atTop atTop ∧
        ∀ n : ℕ, Tendsto (fun t => ‖f (L t) / (L t) ^ n‖) atTop atTop := by
  sorry

end Erdos514
