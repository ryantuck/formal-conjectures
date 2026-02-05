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
# Erdős Problem 436

For prime p and integers k,m ≥ 2, let r(k,m,p) be the minimal r such that
r, r+1, ..., r+m-1 are all k-th power residues modulo p. Define:
  Λ(k,m) = limsup_{p → ∞} r(k,m,p)

Questions:
1. Is Λ(k,2) finite for all k?
2. Is Λ(k,3) finite for all odd k?
3. How large are these values?

Hildebrand: Question 1 answered affirmatively.

Known values: Λ(2,2)=9, Λ(3,2)=77, Λ(4,2)=1224, Λ(5,2)=7888, Λ(6,2)=202124,
Λ(7,2)=1649375, Λ(3,3)=23532.

*Reference:* [erdosproblems.com/436](https://www.erdosproblems.com/436)
-/

open Filter Topology BigOperators

namespace Erdos436

/-- r(k,m,p) is the minimal r for consecutive power residues -/
noncomputable def r (k m p : ℕ) : ℕ :=
  sInf {r : ℕ | ∀ i < m, ∃ x : ZMod p, x ^ k = (r + i : ZMod p)}

/-- Λ(k,m) is the limsup of r(k,m,p) -/
noncomputable def Lambda (k m : ℕ) : ℕ :=
  Filter.limsup (fun p : {p : ℕ // p.Prime} => r k m p.val) atTop

/-- Hildebrand: Λ(k,2) is finite for all k -/
@[category research solved, AMS 11]
theorem erdos_436_hildebrand :
    ∀ k ≥ 2, ∃ M : ℕ, Lambda k 2 ≤ M := by
  sorry

/-- Known exact values for small k,m -/
@[category research solved, AMS 11]
theorem erdos_436_known_values :
    Lambda 2 2 = 9 ∧ Lambda 3 2 = 77 ∧ Lambda 4 2 = 1224 ∧
    Lambda 5 2 = 7888 ∧ Lambda 6 2 = 202124 ∧ Lambda 7 2 = 1649375 ∧
    Lambda 3 3 = 23532 := by
  sorry

end Erdos436
