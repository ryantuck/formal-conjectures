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
# Erdős Problem 426

Is there a graph on n vertices with $\gg 2^{\binom{n}{2}}/n!$ many distinct unique subgraphs?

(A graph H is a unique subgraph of G if there's exactly one copy of H in G.)

Brouwer: Achieved $\gg 2^{\binom{n}{2} - O(n)}/n!$.
Bradač-Christoph (2024): DISPROVED - Maximum is $o(2^{\binom{n}{2}}/n!)$.

*Reference:* [erdosproblems.com/426](https://www.erdosproblems.com/426)
-/

open Filter Topology BigOperators Real

namespace Erdos426

/-- Bradač-Christoph: The conjecture is false -/
@[category research solved, AMS 11]
theorem erdos_426_disproved :
    ∀ ε > 0, ∀ᶠ n : ℕ in atTop,
      ∀ unique_count : ℕ,
        (unique_count : ℝ) < ε * 2^(n * (n-1) / 2) / n.factorial := by
  sorry

end Erdos426
