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
import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
# Erdős Problem 84

*Reference:* [erdosproblems.com/84](https://www.erdosproblems.com/84)
-/

namespace Erdos84

open SimpleGraph

/--
The cycle set of a graph $G$ on $n$ vertices is a set $A\subseteq \{3,\ldots,n\}$ such that there
is a cycle in $G$ of length $\ell$ if and only if $\ell \in A$. Let $f(n)$ count the number of
possible such $A$.

Prove that $f(n)=o(2^n)$.
-/  
def CycleSet {n : ℕ} (G : SimpleGraph (Fin n)) : Set ℕ :=
  { l | ∃ (u : Fin n) (p : G.Walk u u), p.IsCycle ∧ p.length = l }

noncomputable def f (n : ℕ) : ℕ :=
  Nat.card { A : Set ℕ | ∃ (G : SimpleGraph (Fin n)), CycleSet G = A }

@[category research open, AMS 05]
theorem erdos_84_part1 :
    Filter.Tendsto (fun n ↦ (f n : ℝ) / 2 ^ n) Filter.atTop (nhds 0) :=
  sorry

/--
Prove that $f(n)/2^{n/2}\to \infty$.
-/ 
@[category research open, AMS 05]
theorem erdos_84_part2 :
    Filter.Tendsto (fun n ↦ (f n : ℝ) / 2 ^ (n / 2 : ℝ)) Filter.atTop Filter.atTop :=
  sorry

end Erdos84
