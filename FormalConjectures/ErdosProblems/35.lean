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
import FormalConjecturesForMathlib.Data.Set.Density

/-!
# Erdős Problem 35

*Reference:* [erdosproblems.com/35](https://www.erdosproblems.com/35)
-/

namespace Erdos35

open scoped BigOperators Pointwise

/--
Schnirelmann density of a set `A`.
-/
noncomputable def schnirelmannDensity (A : Set ℕ) : ℝ :=
  sInf {((A ∩ Finset.Icc 1 n).ncard : ℝ) / n | n : ℕ}

/--
A set `B` is an additive basis of order `k`.
-/
def IsAdditiveBasis (k : ℕ) (B : Set ℕ) : Prop :=
  Set.univ ⊆ k • B

/--
Let `B` be an additive basis of order `k` containing `0`. Is it true that for every `A`,
$d_s(A+B) \ge \alpha + \alpha(1-\alpha)/k$, where $\alpha = d_s(A)$?

The answer is yes. Plünnecke [Pl70] proved the stronger fact $d_s(A+B) \ge \alpha^{1-1/k}$.

[Pl70] H. Plünnecke, _Eigenschaften und Abschätzungen von Wirkungsfunktionen_,
BMwF-GMD-22, Gesellschaft für Mathematik und Datenverarbeitung, Bonn, 1969.
-/
@[category research solved, AMS 11]
theorem erdos_35 : answer(True) ↔ ∀ k : ℕ, k ≥ 1 →
    ∀ B : Set ℕ, 0 ∈ B → IsAdditiveBasis k B →
    ∀ A : Set ℕ,
    let α := schnirelmannDensity A
    schnirelmannDensity (A + B) ≥ α + α * (1 - α) / k := by
  sorry

end Erdos35
