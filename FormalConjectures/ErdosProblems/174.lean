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
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Erdős Problem 174

*Reference:* [erdosproblems.com/174](https://www.erdosproblems.com/174)

Characterise the Ramsey sets in $\mathbb{R}^n$.
-/

namespace Erdos174

open EuclideanGeometry

/--
A set $A' \subset \mathbb{R}^d$ is a copy of $A \subset \mathbb{R}^n$ if there is an isometry
from $\mathbb{R}^n$ to $\mathbb{R}^d$ mapping $A$ to $A'$.
-/
def IsCopy {n d : ℕ} (A' : Set (EuclideanSpace ℝ (Fin d))) (A : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∃ (f : EuclideanSpace ℝ (Fin n) →ₛₗ[RingHom.id ℝ] EuclideanSpace ℝ (Fin d)),
    Isometry f ∧ f '' A = A'

/--
A finite set $A \subset \mathbb{R}^n$ is Ramsey if, for any $k \geq 1$, there exists some $d$
such that in any $k$-colouring of $\mathbb{R}^d$ there exists a monochromatic copy of $A$.
-/
def IsRamsey {n : ℕ} (A : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  A.Finite ∧ ∀ (k : ℕ) (_ : k ≥ 1), ∃ (d : ℕ), ∀ (f : EuclideanSpace ℝ (Fin d) → Fin k),
    ∃ (A' : Set (EuclideanSpace ℝ (Fin d))),
    IsCopy A' A ∧ (∀ x ∈ A', ∀ y ∈ A', f x = f y)

/--
Characterise the Ramsey sets in $\mathbb{R}^n$.
-/
@[category research open, AMS 5 05]
theorem erdos_174 :
    ∃ (P : ∀ {n : ℕ}, Set (EuclideanSpace ℝ (Fin n)) → Prop),
    ∀ (n : ℕ) (A : Set (EuclideanSpace ℝ (Fin n))),
    A.Finite → (IsRamsey A ↔ P A) := by
  sorry

/--
Every Ramsey set is spherical (it lies on the surface of some sphere).
-/
@[category research solved, AMS 5 05]
theorem erdos_174.spherical :
    ∀ (n : ℕ) (A : Set (EuclideanSpace ℝ (Fin n))),
    IsRamsey A → ∃ (c : EuclideanSpace ℝ (Fin n)) (r : ℝ), ∀ x ∈ A, dist x c = r := by
  sorry

end Erdos174
