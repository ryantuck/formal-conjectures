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
# Erdős Problem 557

Is R(T;k) ≤ kn + O(1) for any tree T on n vertices?

OPEN

*Reference:* [erdosproblems.com/557](https://www.erdosproblems.com/557)
-/

namespace Erdos557

/-- Multicolor tree Ramsey linear bound -/
@[category research open, AMS 05]
theorem tree_ramsey_linear (k : ℕ) (hk : k ≥ 2) :
    ∃ C : ℕ, sorry := by
  sorry

end Erdos557
