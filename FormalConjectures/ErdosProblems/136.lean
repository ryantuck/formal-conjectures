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
import Mathlib.Data.Sym.Sym2

/-!
# Erdős Problem 136

*Reference:* [erdosproblems.com/136](https://www.erdosproblems.com/136)
-/

namespace Erdos136

open Finset Real Filter Topology Sym2 Classical

/--
A coloring of the edges of K_n with c colors.
-/
def EdgeColoring (n c : ℕ) := Sym2 (Fin n) → Fin c

/--
Correct definition using Sym2.
-/
def EveryK4Has5Colors' (n c : ℕ) (χ : EdgeColoring n c) : Prop :=
  ∀ S : Finset (Fin n), S.card = 4 →
    let edges := (S.product S).filter (fun p => p.1 ≠ p.2)
    let colors := edges.image (fun p => χ (Sym2.mk p))
    colors.card ≥ 5

/--
f(n) is the smallest number of colors required.
-/
noncomputable def f (n : ℕ) : ℕ :=
  sInf { c | ∃ χ : EdgeColoring n c, EveryK4Has5Colors' n c χ }

/--
Bennett, Cushman, Dudek, and Pralat [BCDP22] proved that $f(n) \sim \frac{5}{6}n$.
-/
@[category research solved, AMS 05]
theorem erdos_136 :
    answer(sorry) ↔ Tendsto (fun n ↦ (f n : ℝ) / n) atTop (nhds (5 / 6)) := by
  sorry

end Erdos136
