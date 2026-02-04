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
import Mathlib.Data.Real.Basic
import FormalConjectures.Util.ProblemImports

open BigOperators

/--
Let $A=\{a_1,a_2,\ldots\}\subset \mathbb{R}^d$ be an infinite sequence such that $a_{i+1}-a_i$ is a positive unit vector (i.e. is of the form $(0,0,\ldots,1,0,\ldots,0)$). For which $d$ must $A$ contain a three-term arithmetic progression?
-/
def HasThreeTermAP {V : Type*} [Add V] [SMul ℕ V] (A : ℕ → V) : Prop :=
  ∃ i j k, i < j ∧ j < k ∧ A i + A k = 2 • A j

@[category research solved, AMS 05 11]
theorem erdos_problem_192 :
    ∀ (d : ℕ), (∀ (A : ℕ → (Fin d → ℝ)),
      (∀ n, ∃ i, A (n + 1) - A n = Pi.single i 1) →
      HasThreeTermAP A) ↔ d ≤ 3 :=
  sorry
