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
# Erdős Problem 415

Let F(n) be the largest k such that any of the k! orderings appears in some sequence
$\phi(m+1), \ldots, \phi(m+k)$ with $m+k \leq n$.

Is $F(n) = (c+o(1)) \log \log \log n$ for some constant c?
Is the first missing pattern always $\phi(m+1) > \phi(m+2) > \cdots > \phi(m+k)$?

Erdős: F(n) grows like log log log n.

*Reference:* [erdosproblems.com/415](https://www.erdosproblems.com/415)
-/

open Filter Topology BigOperators Real

namespace Erdos415

/-- F(n) is the largest k for which all k! orderings appear in φ sequences up to n -/
noncomputable def F (n : ℕ) : ℕ := sorry

/-- Erdős: F(n) grows like log log log n -/
@[category research open, AMS 11]
theorem erdos_415_growth :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * log (log (log n)) ≤ (F n : ℝ) ∧ (F n : ℝ) ≤ c₂ * log (log (log n)) := by
  sorry

end Erdos415
