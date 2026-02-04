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
# Erdős Problem 278

*Reference:* [erdosproblems.com/278](https://www.erdosproblems.com/278)
-/

open Filter Topology

namespace Erdos278

/--
Given a finite set $A=\{n_1<\cdots<n_r\}$ of positive integers, determine the maximum density
of integers that can be covered by selecting suitable congruences $a_i\pmod{n_i}$.

Simpson (1986): The minimum density is achieved when all $a_i$ are equal, and equals:
$$\sum_i \frac{1}{n_i}-\sum_{i<j}\frac{1}{[n_i,n_j]}+\sum_{i<j<k}\frac{1}{[n_i,n_j,n_k]}-\cdots$$
where $[\cdots]$ denotes the least common multiple.
-/
noncomputable def covering_density (A : Finset ℕ) (a : ℕ → ℕ) : ℝ :=
  iInf fun (N : ℕ) => ((Finset.range N).filter (fun n => ∃ m ∈ A, n % m = a m % m)).card / (N : ℝ)

/--
The minimum density formula (Simpson, 1986).
-/
axiom simpson_density (A : Finset ℕ) : ℝ

/--
Simpson (1986): The minimum density is achieved when all $a_i$ are equal.
-/
@[category research solved, AMS 11]
theorem erdos_278.simpson (A : Finset ℕ) (h : ∀ n ∈ A, n > 0) :
    ∀ a : ℕ → ℕ, covering_density A a ≥ simpson_density A := by
  sorry

/--
The minimum is achieved when all $a_i$ are equal.
-/
@[category research solved, AMS 11]
theorem erdos_278.minimum_equal (A : Finset ℕ) (h : ∀ n ∈ A, n > 0) :
    ∃ a₀ : ℕ, covering_density A (fun _ => a₀) = simpson_density A := by
  sorry

end Erdos278
