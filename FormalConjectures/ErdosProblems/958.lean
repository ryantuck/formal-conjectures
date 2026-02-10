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
# Erdős Problem 958

Characterization of equidistant point sets.

DISPROVED

*Reference:* [erdosproblems.com/958](https://www.erdosproblems.com/958)
-/

open Finset

open scoped Topology Real

namespace Erdos958

/-- Points are collinear -/
def Collinear (A : Finset (ℝ × ℝ)) : Prop :=
  ∃ (a b c : ℝ), a ≠ 0 ∨ b ≠ 0 ∧ ∀ p ∈ A, a * p.1 + b * p.2 = c

/-- Points are concyclic -/
def Concyclic (A : Finset (ℝ × ℝ)) : Prop :=
  ∃ (c : ℝ × ℝ) (r : ℝ), ∀ p ∈ A, dist p c = r

/-- Disproved: characterization of equidistant points -/
@[category research solved, AMS 52]
theorem not_equidistant_characterization :
    ¬ ∀ (A : Finset (ℝ × ℝ)) (n : ℕ),
      A.card = n →
      let dists := (A.product A |>.filter (fun (p, q) => p ≠ q) |>.image (fun (p, q) => dist p q)).sort (· ≤ ·)
      let f := fun d => (A.product A |>.filter (fun (p, q) => dist p q = d)).card
      (dists.length = n - 1 ∧ (dists.map f).toFinset = Finset.range (n - 1) \ {0}) →
      Collinear A ∨ Concyclic A := by
  sorry

end Erdos958
