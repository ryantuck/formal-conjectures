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
# Erdős Problem 866

Estimate gₖ(N) for k pairwise sums.

OPEN

*Reference:* [erdosproblems.com/866](https://www.erdosproblems.com/866)
-/

open Finset Filter Asymptotics

open scoped Topology Real

namespace Erdos866

/-- A set contains k pairwise sums -/
def ContainsKPairwiseSums (A : Finset ℤ) (k : ℕ) : Prop :=
  ∃ b : Fin k → ℤ, ∀ i j : Fin k, i < j →
    (b i + b j) ∈ A

/-- gₖ(N): minimal value such that if |A∩{1,...,2N}| ≥ N + gₖ(N),
    then A contains k pairwise sums -/
noncomputable def g_k (k N : ℕ) : ℕ :=
  sInf {g : ℕ | ∀ A : Finset ℤ,
    (A ∩ Finset.Icc 1 (2*N)).card ≥ N + g →
    ContainsKPairwiseSums A k}

/-- Main question: estimate gₖ(N) -/
@[category research open, AMS 11]
theorem estimate_g_k (k : ℕ) (hk : k ≥ 3) :
    ∃ f : ℕ → ℝ, (fun N => (g_k k N : ℝ)) ~[Filter.atTop] f := by
  sorry

/-- Known values: g₃(N) = 2 -/
@[category research solved, AMS 11]
theorem g_3_value : ∀ N : ℕ, g_k 3 N = 2 := by
  sorry

/-- Known bound: g₄(N) ≤ 2032 -/
@[category research solved, AMS 11]
theorem g_4_bound : ∀ N : ℕ, g_k 4 N ≤ 2032 := by
  sorry

/-- General upper bound: gₖ(N) ≪ₖ N^{1-2^{-k}} -/
@[category research solved, AMS 11]
theorem general_upper_bound (k : ℕ) (hk : k ≥ 3) :
    ∃ C : ℝ, C > 0 ∧ ∀ N : ℕ, N ≥ 1 →
      (g_k k N : ℝ) ≤ C * (N : ℝ) ^ (1 - (2 : ℝ) ^ (-(k : ℝ))) := by
  sorry

end Erdos866
