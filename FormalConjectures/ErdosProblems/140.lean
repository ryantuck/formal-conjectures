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
# Erdős Problem 140

*Reference:* [erdosproblems.com/140](https://www.erdosproblems.com/140)
-/

namespace Erdos140

open Finset Filter Real Classical

/--
A set A is free of 3-term arithmetic progressions if no three distinct elements form an AP.
-/
def IsAP3Free (A : Finset ℕ) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x < y ∧ y < z → x + z ≠ 2 * y

/--
r_3(N) is the size of the largest AP-3 free subset of {1, ..., N}.
-/
noncomputable def r3 (N : ℕ) : ℕ :=
  sup (filter (fun A => A ⊆ Icc 1 N ∧ IsAP3Free A) (powerset (Icc 1 N))) card

/--
The conjecture is that $r_3(N) \ll N / (\log N)^C$ for every $C > 0$.
Kelley and Meka [KeMe23] proved this.
-/
@[category research solved, AMS 11]
theorem erdos_140 :
    ∀ C > 0, ∃ K > 0, ∀ N ≥ 2, (r3 N : ℝ) ≤ K * (N : ℝ) / (log N) ^ C := by
  sorry

end Erdos140
