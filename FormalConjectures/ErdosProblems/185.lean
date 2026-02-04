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
# Erdős Problem 185

*Reference:* [erdosproblems.com/185](https://www.erdosproblems.com/185)

Let $f_3(n)$ be the maximal size of a subset of $\{0,1,2\}^n$ which contains no three points
on a line. Is it true that $f_3(n)=o(3^n)$?
-/

namespace Erdos185

open Finset Real Classical

/--
A combinatorial line in $[3]^n$ is a set of 3 points where some coordinates are fixed
and the rest (the wildcard coordinates) all take the same value.
-/
def IsCombinatorialLine {n : ℕ} (L : Finset (Fin n → Fin 3)) : Prop :=
  ∃ (S : Finset (Fin n)) (_ : S.Nonempty) (c : Fin n → Fin 3),
    L = univ.image fun (i : Fin 3) =>
      fun (j : Fin n) => if j ∈ S then i else c j

/--
$f_3(n)$ is the maximal size of a subset of $\{0,1,2\}^n$ containing no combinatorial line.
-/
noncomputable def f3 (n : ℕ) : ℕ :=
  sSup { k | ∃ (A : Finset (Fin n → Fin 3)), k = A.card ∧ ∀ (L : Finset (Fin n → Fin 3)), L ⊆ A → ¬ IsCombinatorialLine L }

/--
Erdős and Moser asked if $f_3(n) = o(3^n)$.
Confirmed by the density Hales-Jewett theorem [FuKa91].
-/
@[category research solved, AMS 05 11]
theorem erdos_185 :
    answer(True) ↔ Asymptotics.IsLittleO Filter.atTop (fun n ↦ (f3 n : ℝ)) (fun n ↦ (3 ^ n : ℝ)) := by
  sorry

end Erdos185
