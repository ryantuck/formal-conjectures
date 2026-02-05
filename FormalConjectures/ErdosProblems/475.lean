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
# Erdős Problem 475

Let p be a prime. Given any finite set A ⊆ 𝔽ₚ\{0}, is there always a rearrangement
A = {a₁,...,aₜ} such that all partial sums ∑_{k≤m} aₖ are distinct, for all 1 ≤ m ≤ t?

Graham proved it for t = p-1.
Costa-Pellegrini: Proved for t ≤ 12.
Hicks-Ollis-Schmitt: Proved for p-3 ≤ t ≤ p-1.
Kravitz: Proved for t ≤ log p / log log p.

*Reference:* [erdosproblems.com/475](https://www.erdosproblems.com/475)
-/

open Filter Topology BigOperators Real Classical

namespace Erdos475

/-- Graham-Erdős conjecture on valid orderings -/
@[category research open, AMS 11]
theorem erdos_475 :
    ∀ p : ℕ, p.Prime → ∀ A : Finset (ZMod p), 0 ∉ A → A.Nonempty →
      ∃ perm : Fin A.card → ZMod p, Function.Bijective perm ∧
        (∀ i : Fin A.card, perm i ∈ A) ∧
        ∀ i j : Fin A.card, i ≠ j →
          (Finset.univ.filter (· ≤ i)).sum perm ≠
          (Finset.univ.filter (· ≤ j)).sum perm := by
  sorry

end Erdos475
