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
# Erdős Problem 179

*Reference:* [erdosproblems.com/179](https://www.erdosproblems.com/179)

Let $1 \leq k < \ell$ be integers and define $F_k(N, \ell)$ to be minimal such that every set
$A \subset \mathbb{N}$ of size $N$ which contains at least $F_k(N, \ell)$ many
$k$-term arithmetic progressions must contain an $\ell$-term arithmetic progression.

Is it true that $F_3(N, 4) = o(N^2)$?
Is it true that for every $\ell > 3$, $\lim_{N \to \infty} \frac{\log F_3(N, \ell)}{\log N} = 2$?
-/

namespace Erdos179

open Finset

/--
A set is a $k$-term arithmetic progression.
-/
def IsAP (P : Finset ℕ) (k : ℕ) : Prop :=
  ∃ (a d : ℕ), d > 0 ∧ P = Finset.image (fun i => a + i * d) (Finset.range k)

/--
The number of $k$-term arithmetic progressions contained in a set $A$.
-/
noncomputable def CountAP (A : Finset ℕ) (k : ℕ) : ℕ :=
  letI := Classical.propDecidable
  (powerset A).filter (IsAP · k) |>.card

/--
$F_k(N, \ell)$ is the minimal $m$ such that any set $A$ of size $N$ with at least $m$
$k$-term APs must contain an $\ell$-term AP.
-/
noncomputable def F (k N ℓ : ℕ) : ℕ :=
  sInf { m : ℕ | ∀ (A : Finset ℕ), A.card = N →
    CountAP A k ≥ m → ∃ (P : Finset ℕ), P ⊆ A ∧ IsAP P ℓ }

/--
Is it true that $F_3(N, 4) = o(N^2)$?
-/
@[category research solved, AMS 05 11]
theorem erdos_179_1 :
    Asymptotics.IsLittleO Filter.atTop (fun N => (F 3 N 4 : ℝ)) (fun N => (N : ℝ) ^ 2) := by
  sorry

/--
Is it true that for every $\ell > 3$, $\lim_{N \to \infty} \frac{\log F_3(N, \ell)}{\log N} = 2$?
-/
@[category research solved, AMS 05 11]
theorem erdos_179_2 :
    ∀ (ℓ : ℕ), ℓ > 3 →
    Filter.Tendsto (fun N => Real.log (F 3 N ℓ) / Real.log N) Filter.atTop (nhds 2) := by
  sorry

end Erdos179
