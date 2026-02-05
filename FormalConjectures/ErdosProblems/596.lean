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
# Erdős Problem 596

For which pairs of graphs (G₁, G₂) is it true that: (a) for every n ≥ 1 there exists
a G₁-free graph H such that every n-coloring of H's edges contains a monochromatic G₂,
AND (b) for every G₁-free graph H there exists a countably infinite coloring with no
monochromatic G₂?

OPEN (known example: G₁ = C₄, G₂ = C₆)

*Reference:* [erdosproblems.com/596](https://www.erdosproblems.com/596)
-/

open SimpleGraph

open scoped Topology Real

namespace Erdos596

variable {α β : Type*}

/-- Characterize (G₁, G₂) pairs for finite/infinite Ramsey dichotomy (simplified) -/
@[category research open, AMS 05]
theorem ramsey_dichotomy_pairs (G₁ G₂ : SimpleGraph ℕ) (answer : Prop) :
    answer ↔ sorry := by
  sorry

end Erdos596
