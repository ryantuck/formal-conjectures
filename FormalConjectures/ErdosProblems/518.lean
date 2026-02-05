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
# Erdős Problem 518

Is it true that, in any two-colouring of the edges of K_n, there exist √n monochromatic paths,
all of the same colour, which cover all vertices?

SOLVED: Pokrovskiy, Versteegen, and Williams (2024).

*Reference:* [erdosproblems.com/518](https://www.erdosproblems.com/518)
-/

open Finset

namespace Erdos518

/-- Monochromatic path covering in 2-colored complete graphs -/
@[category research solved, AMS 05]
theorem monochromatic_path_cover :
    ∀ n : ℕ, ∃ k : ℕ, k ≤ Nat.sqrt n + 1 →
      ∀ (χ : Sym2 (Fin n) → Fin 2),
        ∃ (color : Fin 2) (paths : Finset (List (Fin n))),
          paths.card ≤ k ∧
          (∀ p ∈ paths, p.Chain' (fun u v => χ s(u, v) = color)) ∧
          (∀ v : Fin n, ∃ p ∈ paths, v ∈ p) := by
  sorry

end Erdos518
