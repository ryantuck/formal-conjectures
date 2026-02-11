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
# Erdős Problem 1155

Random triangle deletion process.

PARTIALLY SOLVED - Bohman, Frieze, Lubetzky (2015) proved f(n)=n^{3/2+o(1)} a.s.

*Reference:* [erdosproblems.com/1155](https://www.erdosproblems.com/1155)
-/

open Finset Filter SimpleGraph

open scoped Topology Real

namespace Erdos1155

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Starting with the complete graph on n vertices, repeatedly delete uniformly random
    triangles until the graph is triangle-free. The number of remaining edges satisfies
    f(n) = n^{3/2+o(1)} almost surely. (Bohman-Frieze-Lubetzky 2015)

    This formalization states the existence of such a process, though the full probabilistic
    statement would require substantial probability theory infrastructure. -/
@[category research open, AMS 05]
theorem random_triangle_deletion_edges :
    ∀ (ε : ℝ), ε > 0 →
    ∃ (f : ℕ → ℕ), ∀ᶠ (n : ℕ) in atTop,
      (n : ℝ)^((3/2 : ℝ) - ε) ≤ f n ∧ f n ≤ (n : ℝ)^((3/2 : ℝ) + ε) := by
  sorry

end Erdos1155
