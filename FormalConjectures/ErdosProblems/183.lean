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
import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
# Erdős Problem 183

*Reference:* [erdosproblems.com/183](https://www.erdosproblems.com/183)

Let $R(3;k)$ be the minimal $n$ such that if the edges of $K_n$ are coloured with $k$ colours then
there must exist a monochromatic triangle. Determine
$$ \lim_{k	o \infty}R(3;k)^{1/k}. $$
-/

namespace Erdos183

open SimpleGraph Finset Real Classical

/--
$R(3; k)$ is the minimal $n$ such that any $k$-colouring of the edges of $K_n$
contains a monochromatic triangle.
-/
noncomputable def multicolorRamsey3 (k : ℕ) : ℕ :=
  sInf { n | ∀ (col : Sym2 (Fin n) → Fin k), ∃ (i : Fin k),
    ∃ (a b c : Fin n), a ≠ b ∧ b ≠ c ∧ a ≠ c ∧
    col (Sym2.mk (a, b)) = i ∧ col (Sym2.mk (b, c)) = i ∧ col (Sym2.mk (a, c)) = i }

/--
Erdős asked for the value of the limit of $R(3; k)^{1/k}$ as $k 	o \infty$.
He offered $100 for showing this limit is finite.
-/
@[category research open, AMS 05]
theorem erdos_183 :
    ∃ L, Filter.Tendsto (fun k ↦ (multicolorRamsey3 k : ℝ) ^ (1 / k : ℝ)) Filter.atTop (nhds L) := by
  sorry

end Erdos183
