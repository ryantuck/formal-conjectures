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
# Erdős Problem 177

*Reference:* [erdosproblems.com/177](https://www.erdosproblems.com/177)

Find the smallest $h(d)$ such that the following holds. There exists a function
$f: \mathbb{N} 	o \{-1, 1\}$ such that, for every $d \geq 1$,
$$ \max_{P_d} \left\lvert \sum_{n \in P_d} f(n) ightvert \leq h(d), $$
where $P_d$ ranges over all finite arithmetic progressions with common difference $d$.
-/

namespace Erdos177

open Finset

/--
A set is a finite arithmetic progression with common difference $d$.
-/
def IsAPWithDiff (P : Finset ℕ) (d : ℕ) : Prop :=
  ∃ (a k : ℕ), k > 0 ∧ P = Finset.image (fun i => a + i * d) (Finset.range k)

/--
$h(d)$ is the smallest value such that there exists a $\{-1, 1\}$-colouring of $\mathbb{N}$
where every finite AP with common difference $d$ has discrepancy at most $h(d)$.
-/
noncomputable def h (d : ℕ) : ℝ :=
  sInf { c : ℝ | ∃ (f : ℕ → ℤ), (∀ i, f i = 1 ∨ f i = -1) ∧
    ∀ (P : Finset ℕ), IsAPWithDiff P d → |∑ i ∈ P, f i| ≤ c }

/--
The problem is to characterize the smallest $h(d)$.
-/
@[category research open, AMS 05 11]
theorem erdos_177 :
    ∃ (H : ℕ → ℝ), ∀ (d : ℕ), d ≥ 1 → h d = H d := by
  sorry

end Erdos177
