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
# Erdős Problem 1005

Farey sequence ordering problem.

OPEN

STATUS: OPEN

*Reference:* [erdosproblems.com/1005](https://www.erdosproblems.com/1005)
-/

open Finset Filter

open scoped Topology Real

namespace Erdos1005

/-- Farey sequence of order n (sorted reduced fractions a/b with 0 ≤ a ≤ b ≤ n) -/
noncomputable def fareySequence (n : ℕ) : List ℚ :=
  (((Icc 0 n).product (Icc 1 n)).toList.filterMap (fun (a, b) =>
    if a ≤ b && a.gcd b = 1 then some ((a : ℚ) / b) else none
  )).mergeSort (· < ·)

/-- f(n) is the largest integer such that if 1 ≤ k < l ≤ k + f(n) then
    (a_k - a_l)(b_k - b_l) ≥ 0, where a_i/b_i is the i-th Farey fraction of order n. -/
noncomputable def f (n : ℕ) : ℕ :=
  if n < 4 then 0 else
  let L := fareySequence n
  let N := L.length
  open scoped Classical in
  Nat.findGreatest (fun m =>
    ∀ (k l : ℕ) (hk : k < N) (hl : l < N), k < l → l ≤ k + m →
    ((L.get ⟨k, hk⟩).num - (L.get ⟨l, hl⟩).num) *
    ((L.get ⟨k, hk⟩).den - (L.get ⟨l, hl⟩).den : ℤ) ≥ 0
  ) N

/--
English version: Estimate f(n) - in particular, is there a constant c > 0 such that
    f(n) = (c + o(1))n for all large n? -/
@[category research open, AMS 11]
theorem farey_ordering_linear : answer(sorry) ↔ ∃ (c : ℝ), 0 < c ∧
      Tendsto (fun n => (f n : ℝ) / (c * n)) atTop (nhds 1) := by
  sorry

end Erdos1005
