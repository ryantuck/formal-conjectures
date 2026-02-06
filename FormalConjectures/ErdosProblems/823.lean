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
# Erdős Problem 823

Sequences with σ(n_k) = σ(m_k).

SOLVED

*Reference:* [erdosproblems.com/823](https://www.erdosproblems.com/823)
-/

open Finset Nat

open scoped Topology Real

namespace Erdos823

/-- Sum of divisors -/
def sigma (n : ℕ) : ℕ := sorry

/-- Sequences with ratio α and equal sigma -/
@[category research solved, AMS 11]
theorem sigma_equal_sequences (α : ℝ) (hα : α ≥ 1) :
    ∃ (n : ℕ → ℕ) (m : ℕ → ℕ),
      StrictMono n ∧ StrictMono m ∧
      Filter.Tendsto (fun k => (n k : ℝ) / m k) Filter.atTop (nhds α) ∧
      ∀ k, sigma (n k) = sigma (m k) := by
  sorry

end Erdos823
