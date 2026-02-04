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
# Erdős Problem 215

*Reference:* [erdosproblems.com/215](https://www.erdosproblems.com/215)
-/

namespace Erdos215

/--
The set of lattice points $\mathbb{Z}^2$ embedded in $\mathbb{R}^2$.
-/
noncomputable def LatticePoints : Set (ℝ × ℝ) :=
  { p | ∃ (x y : ℤ), p = (↑x, ↑y) }

/--
A set $S \subset \mathbb{R}^2$ is a Steinhaus set if every congruent copy of $S$
intersects the lattice exactly once.
-/
def IsSteinhausSet (S : Set (ℝ × ℝ)) : Prop :=
  ∀ (f : (ℝ × ℝ) ≃ᵢ (ℝ × ℝ)), ∃! p, p ∈ f '' S ∧ p ∈ LatticePoints

/--
Jackson and Mauldin [JaMa02] proved that a Steinhaus set exists.

[JaMa02] Jackson, S. and Mauldin, R. D., _On a lattice problem of Steinhaus_,
Journal of the American Mathematical Society (2002).
-/
@[category research solved, AMS 52]
theorem erdos_215 : ∃ (S : Set (ℝ × ℝ)), IsSteinhausSet S := by
  sorry

end Erdos215
