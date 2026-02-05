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
# Erdős Problem 481

Let a₁,...,aᵣ, b₁,...,bᵣ ∈ ℕ with ∑ᵢ 1/aᵢ > 1. For a sequence A = (x₁,...,xₙ), define
T(A) as the sequence (aᵢxⱼ + bᵢ) for 1 ≤ j ≤ n, 1 ≤ i ≤ r.

Prove that if A₁ = (1) and Aᵢ₊₁ = T(Aᵢ), then some Aₖ must contain repeated elements.

Klarner: PROVED (Lean verified).

*Reference:* [erdosproblems.com/481](https://www.erdosproblems.com/481)
-/

open Filter Topology BigOperators Real Classical

namespace Erdos481

/-- Transform T applied to a sequence -/
def T {r : ℕ} (a b : Fin r → ℕ) (A : List ℕ) : List ℕ :=
  (List.finRange r).flatMap (fun i => A.map (fun x => a i * x + b i))

/-- Klarner: Iteration eventually produces duplicates -/
@[category research solved, AMS 11]
theorem erdos_481_klarner :
    ∀ r : ℕ, ∀ a b : Fin r → ℕ,
      ((Finset.univ : Finset (Fin r)).sum (fun i => (1 : ℝ) / (a i)) > 1) →
      ∃ k : ℕ, ¬(Nat.iterate (T a b) k [1]).Nodup := by
  sorry

end Erdos481
