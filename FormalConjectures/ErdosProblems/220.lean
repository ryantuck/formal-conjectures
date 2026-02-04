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
# Erdős Problem 220

*Reference:* [erdosproblems.com/220](https://www.erdosproblems.com/220)
-/

open Finset

namespace Erdos220

/--
The set of integers $1 \le m < n$ such that $(m, n) = 1$.
-/
noncomputable def CoprimeResidues (n : ℕ) : List ℕ :=
  ((range n).filter (fun m ↦ m.Coprime n ∧ m ≥ 1)).toList.mergeSort (· ≤ ·)

/--
The sum of $\gamma$-powers of the gaps between consecutive coprime residues.
-/
noncomputable def gapSum (n : ℕ) (γ : ℝ) : ℝ :=
  let L := CoprimeResidues n
  ((L.zip (L.drop 1)).map (fun p ↦ ((p.2 : ℝ) - p.1) ^ γ)).sum

/--
Is it true that $\sum_{1 \le k < \phi(n)} (a_{k+1} - a_k)^2 \ll \frac{n^2}{\phi(n)}$?
-/
@[category research solved, AMS 11]
theorem erdos_220 : ∃ C > 0, ∀ n ≥ 1, gapSum n 2 ≤ C * (n^2 : ℝ) / Nat.totient n := by
  sorry

/--
Montgomery and Vaughan [MoVa86] proved that for any $\gamma \ge 1$
$$ \sum_{1 \le k < \phi(n)} (a_{k+1} - a_k)^\gamma \ll \frac{n^\gamma}{\phi(n)^{\gamma-1}}. $$

[MoVa86] Montgomery, H. L. and Vaughan, R. C., _On the distribution of reduced residues_.
  Annals of Math. (1986), 311-333.
-/
@[category research solved, AMS 11]
theorem erdos_220.variants.general : ∀ γ ≥ 1, ∃ C > 0, ∀ n ≥ 1,
    gapSum n γ ≤ C * (n : ℝ)^γ / (Nat.totient n : ℝ)^(γ - 1) := by
  sorry

end Erdos220
