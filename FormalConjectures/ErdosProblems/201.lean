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
import FormalConjecturesForMathlib.Combinatorics.AP.Basic

/-!
# Erdős Problem 201

*Reference:* [erdosproblems.com/201](https://www.erdosproblems.com/201)
-/

open Filter
open scoped Topology Real

namespace Erdos201

/--
`R k N` is the size of the largest subset of `{1, ..., N}` without a `k`-term arithmetic progression.
This is the same as `Set.IsAPOfLengthFree.maxCard k N`.
-/
noncomputable abbrev R (k : ℕ) (N : ℕ) : ℕ := Set.IsAPOfLengthFree.maxCard k N

/--
`G k N` is the maximum size such that any set of `N` integers contains a `k`-AP-free subset of
size at least `G k N`.
-/
noncomputable def G (k : ℕ) (N : ℕ) : ℕ :=
  sInf { (sSup {Finset.card B | (B) (_ : B ⊆ A) (_ : B.toSet.IsAPOfLengthFree k)}) | (A : Finset ℤ) (_ : A.card = N) }

/--
Is it true that
$$ \lim_{N	o \infty}\frac{R_3(N)}{G_3(N)}=1? $$
-/
@[category research open, AMS 11]
theorem erdos_201 : Tendsto (fun N => (R 3 N : ℝ) / (G 3 N : ℝ)) atTop (𝓝 1) := by
  sorry

end Erdos201
