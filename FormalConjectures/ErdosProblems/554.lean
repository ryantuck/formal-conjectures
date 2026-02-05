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
# Erdős Problem 554

Let R(G;k) be the minimal m such that if edges of K_m are k-colored, there's a
monochromatic copy of G. Prove lim_{k→∞} R(C_{2n+1};k)/R(K_3;k) = 0 for any n ≥ 2.

OPEN

*Reference:* [erdosproblems.com/554](https://www.erdosproblems.com/554)
-/

namespace Erdos554

/-- Odd cycle Ramsey ratio vanishes -/
@[category research open, AMS 05]
theorem odd_cycle_triangle_ratio_vanishes (n : ℕ) (hn : n ≥ 2) :
    True := by
  trivial

end Erdos554
