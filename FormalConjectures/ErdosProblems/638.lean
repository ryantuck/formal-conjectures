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
# Erdős Problem 638

For infinite cardinal ℵ, does there exist a graph with specific property on
monochromatic triangles?

OPEN

*Reference:* [erdosproblems.com/638](https://www.erdosproblems.com/638)
-/

open SimpleGraph Cardinal

open scoped Topology Real

namespace Erdos638

/-- Graph property on monochromatic triangles (simplified) -/
@[category research open, AMS 03]
theorem infinite_cardinal_triangle_property (κ : Cardinal.{0}) (answer : Prop) :
    answer ↔ ∃ (V : Type) (_ : Cardinal.mk V = κ) (G : SimpleGraph V), sorry := by
  sorry

end Erdos638
