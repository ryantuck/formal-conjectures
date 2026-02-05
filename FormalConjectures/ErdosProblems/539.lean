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
# Erdős Problem 539

Let h(n) be such that for any set A ⊆ ℕ of size n, the set {a/gcd(a,b) : a,b ∈ A}
has size at least h(n). Estimate h(n).

Known: n^(1/2) ≪ h(n) ≪ n^(2/3) by Erdős-Szemerédi and Freiman-Lev.

OPEN

*Reference:* [erdosproblems.com/539](https://www.erdosproblems.com/539)
-/

open Nat Finset Real

namespace Erdos539

/-- Size of gcd quotient set -/
noncomputable def h (n : ℕ) : ℕ :=
  sInf {k : ℕ | ∀ (A : Finset ℕ),
    (∀ a ∈ A, a > 0) → A.card = n →
    (A.biUnion fun a => A.image fun b => a / Nat.gcd a b).card ≥ k}

/-- Lower bound for h(n) -/
@[category research open, AMS 11]
theorem h_lower_bound :
    ∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, n ≥ 2 → h n ≥ ⌊c * Real.sqrt n⌋₊ := by
  sorry

/-- Upper bound for h(n) -/
@[category research open, AMS 11]
theorem h_upper_bound :
    ∃ C : ℝ, C > 0 ∧ ∀ᶠ n in Filter.atTop, h n ≤ ⌊C * n ^ (2/3 : ℝ)⌋₊ := by
  sorry

/-- Estimate h(n) -/
@[category research open, AMS 11]
theorem estimate_h :
    answer(sorry) ↔ ∃ α : ℝ, 1/2 < α ∧ α < 1 ∧
      ∃ c C : ℝ, c > 0 ∧ C > 0 ∧ ∀ᶠ (n : ℕ) in Filter.atTop,
        ⌊c * (n : ℝ) ^ α⌋₊ ≤ h n ∧ h n ≤ ⌊C * (n : ℝ) ^ α⌋₊ := by
  sorry

end Erdos539
