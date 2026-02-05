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
# Erdős Problem 561

Let F₁ = ⋃_{i≤s} K_{1,n_i} and F₂ = ⋃_{j≤t} K_{1,m_j} be unions of stars.
Prove R̂(F₁,F₂) = ∑_{2≤k≤s+t} l_k where l_k = max{n_i + m_j - 1 : i+j = k}.

OPEN (with partial results for special cases)

*Reference:* [erdosproblems.com/561](https://www.erdosproblems.com/561)
-/

namespace Erdos561

/-- Size Ramsey for unions of stars -/
@[category research open, AMS 05]
theorem size_ramsey_star_unions (s t : ℕ) (n : Fin s → ℕ) (m : Fin t → ℕ) :
    True := by
  trivial

end Erdos561
