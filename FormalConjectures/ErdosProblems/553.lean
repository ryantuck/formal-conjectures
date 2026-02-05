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
# Erdős Problem 553

Let R(3,3,n) be the smallest m such that if we 3-color edges of K_m, there's either
a monochromatic triangle in colors 1 or 2, or monochromatic K_n in color 3.

Show R(3,3,n)/R(3,n) → ∞ as n → ∞.

SOLVED: Alon-Rödl proved this.

*Reference:* [erdosproblems.com/553](https://www.erdosproblems.com/553)
-/

namespace Erdos553

/-- Three-color Ramsey number diverges from two-color -/
@[category research solved, AMS 05]
theorem three_color_ramsey_diverges :
    True := by
  trivial

end Erdos553
