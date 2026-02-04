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
import FormalConjecturesForMathlib.Combinatorics.AP.Basic

/-!
# Erdős Problem 169

*Reference:* [erdosproblems.com/169](https://www.erdosproblems.com/169)

Let $k\geq 3$ and $f(k)$ be the supremum of $\sum_{n\in A}\frac{1}{n}$ as $A$ ranges over
all sets of positive integers which do not contain a $k$-term arithmetic progression.
Estimate $f(k)$.

Is
$$\lim_{k	o \infty}\frac{f(k)}{\log W(k)}=\infty$$
where $W(k)$ is the van der Waerden number?
-/

namespace Erdos169

open Set Filter Real

/--
$f(k)$ is the supremum of $\sum_{n\in A} 1/n$ as $A$ ranges over all sets of positive integers
which do not contain a $k$-term arithmetic progression.
-/
noncomputable def f (k : ℕ) : ℝ :=
  sSup { s | ∃ (A : Set ℕ), (∀ n ∈ A, n > 0) ∧ (A.IsAPOfLengthFree k) ∧ 
    (HasSum (fun n : A ↦ 1 / (n : ℝ)) s) }

/--
The van der Waerden number $W(k)$ is the smallest $N$ such that any 2-coloring of $\{1, \dots, N\}$
contains a monochromatic arithmetic progression of length $k$.
-/
def monoAP_guarantee_set (r k : ℕ) : Set ℕ :=
  { N | ∀ coloring : Finset.Icc 1 N → Fin r, ContainsMonoAPofLength coloring k }

noncomputable def W (k : ℕ) : ℕ := sInf (monoAP_guarantee_set 2 k)

/--
Is $\lim_{k	o \infty}\frac{f(k)}{\log W(k)}=\infty$?
-/
@[category research open, AMS 05]
theorem erdos_169 : answer(sorry) ↔ 
    Tendsto (fun k ↦ (f k) / (log (W k))) atTop atTop := by
  sorry

end Erdos169
