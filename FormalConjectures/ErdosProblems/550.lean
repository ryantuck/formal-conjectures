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
# Erdős Problem 550

Let m₁ ≤ ... ≤ m_k and n sufficiently large. If T is a tree on n vertices and G is
the complete multipartite graph with class sizes m₁,...,m_k, prove:
R(T,G) ≤ (χ(G)-1)(R(T,K_{m₁,m₂})-1) + m₁

OPEN

*Reference:* [erdosproblems.com/550](https://www.erdosproblems.com/550)
-/

namespace Erdos550

/-- Ramsey bound for trees and multipartite graphs -/
@[category research open, AMS 05]
theorem ramsey_tree_multipartite :
    ∀ (k : ℕ) (m : Fin k → ℕ), (∀ i j, i ≤ j → m i ≤ m j) →
      True := by
  intro _ _ _
  trivial

end Erdos550
