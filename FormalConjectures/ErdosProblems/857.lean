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
# Erdős Problem 857

Sunflower lemma - estimate m(n,k).

OPEN

*Reference:* [erdosproblems.com/857](https://www.erdosproblems.com/857)
-/

open Finset Filter Asymptotics

open scoped Topology Real

namespace Erdos857

variable {α : Type*} [DecidableEq α]

/-- A k-sunflower: k sets with pairwise identical intersection -/
def IsSunflower (F : Finset (Finset α)) (k : ℕ) : Prop :=
  ∃ (S : Finset (Finset α)) (core : Finset α),
    S ⊆ F ∧ S.card = k ∧
    ∀ A B, A ∈ S → B ∈ S → A ≠ B → A ∩ B = core

/-- m(n,k): minimal m such that any m subsets of [n] contain a k-sunflower -/
noncomputable def m (n k : ℕ) : ℕ :=
  sInf {m : ℕ | ∀ F : Finset (Finset (Fin n)), F.card ≥ m → IsSunflower F k}

/-- Main conjecture: estimate m(n,k) or give asymptotic formula -/
@[category research open, AMS 5]
theorem sunflower_bound_conjecture (k : ℕ) (hk : k ≥ 2) :
    ∃ f : ℕ → ℝ, (fun n => (m n k : ℝ)) ~[atTop] f := by
  sorry

/-- Known result for k=3 (Naslund-Sawin) -/
@[category research solved, AMS 5]
theorem naslund_sawin_k3 :
    ∃ C : ℝ, C = 3 / (2 : ℝ) ^ (2/3) ∧
      ∀ ε > 0, ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ →
        (m n 3 : ℝ) ≤ C ^ ((1 + ε) * n) := by
  sorry

end Erdos857
