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
import Mathlib.Data.Nat.Totient
import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Erdős Problem 50

*Reference:* [erdosproblems.com/50](https://www.erdosproblems.com/50)
-/

namespace Erdos50

open Set Nat Classical

open scoped Topology

/--
Schoenberg proved that for every $c \in [0, 1]$ the density of
$\{n \in \mathbb{N} : \phi(n) < cn\}$ exists. Let this density be denoted by $f(c)$.
-/
noncomputable def SchoenbergDensity (c : ℝ) : ℝ :=
  if h : ∃ α, {n : ℕ | φ n < c * n}.HasDensity α then Classical.choose h else 0

/--
Is it true that there are no $x$ such that $f'(x)$ exists and is positive?

Erdős [Er95] could prove the distribution function is purely singular.
-/
@[category research open, AMS 11]
theorem erdos_50 : answer(sorry) ↔ ¬ ∃ x : ℝ, HasDerivAt SchoenbergDensity (deriv SchoenbergDensity x) x ∧
    deriv SchoenbergDensity x > 0 := by
  sorry

end Erdos50
