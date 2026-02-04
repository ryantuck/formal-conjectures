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
# Erdős Problem 191

*Reference:* [erdosproblems.com/191](https://www.erdosproblems.com/191)

Let $C>0$ be arbitrary. Is it true that, if $n$ is sufficiently large depending on $C$, then in
any $2$-colouring of $\binom{\{2,\ldots,n\}}{2}$ there exists some $X\subset \{2,\ldots,n\}$ such
that $\binom{X}{2}$ is monochromatic and
$$ \sum_{x\in X}\frac{1}{\log x}\geq C? $$
-/

namespace Erdos191

open Finset Real Classical

/--
A set of pairs from X.
-/
noncomputable def Pairs {V : Type*} (X : Finset V) : Finset (Sym2 V) :=
  (X.product X).filter (fun p ↦ p.1 ≠ p.2) |>.image (fun p ↦ Sym2.mk p)

/--
X is monochromatic under coloring c if all pairs in X have the same color.
-/
noncomputable def IsMonochromatic {V α : Type*} (X : Finset V) (c : Sym2 V → α) : Prop :=
  ∃ color, ∀ e ∈ Pairs X, c e = color

/--
Erdős and Graham asked if for any C > 0, for large n, any 2-colouring of edges
of {2, ..., n} contains a monochromatic subset X with sum_{x in X} 1/log x >= C.
Confirmed by Rödl [Ro03].
-/
@[category research solved, AMS 05]
theorem erdos_191 :
    ∀ (C : ℝ), ∃ (N₀ : ℕ), ∀ (n : ℕ), N₀ ≤ n →
    let V := { x : ℕ // 2 ≤ x ∧ x ≤ n }
    ∀ (col : Sym2 V → Fin 2),
    ∃ (X : Finset V),
    IsMonochromatic X col ∧
    (∑ x ∈ X, 1 / log (x.val : ℝ)) ≥ C := by
  sorry

end Erdos191
