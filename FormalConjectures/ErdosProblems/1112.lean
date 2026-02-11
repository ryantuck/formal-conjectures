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
# Erdős Problem 1112

Lacunary sequences and sumset gaps.

OPEN

*Reference:* [erdosproblems.com/1112](https://www.erdosproblems.com/1112)
-/

open Finset Filter

open scoped Real

namespace Erdos1112

/-- Lacunary sequences and sumset gaps.
    Asks about lacunary sequences whose sumsets have large gaps. -/
@[category research open, AMS 11]
theorem lacunary_sumset_gaps :
    ∃ (A : Set ℕ),
      (∀ᶠ n in atTop, ∀ a ∈ A, a < n → ∀ a' ∈ A, a' < n → a' ≠ a → (a' : ℝ) / a ≥ 2) ∧
      (∃ gap : ℕ, ∀ n, ∃ k, ∀ m ∈ Set.Icc k (k + gap), m ∉ {a + b | (a ∈ A) (b ∈ A)}) := by
  sorry

end Erdos1112
