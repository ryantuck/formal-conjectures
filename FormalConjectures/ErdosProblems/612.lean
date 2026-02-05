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
# Erdős Problem 612

Prove diameter bounds for connected graphs with n vertices and minimum degree d
that are K_{2r}-free or K_{2r+1}-free.

OPEN

*Reference:* [erdosproblems.com/612](https://www.erdosproblems.com/612)
-/

open SimpleGraph

open scoped Topology Real

namespace Erdos612

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Diameter bound for K_k-free graphs with min degree d -/
@[category research open, AMS 05]
theorem diameter_bound_k_free (k d : ℕ) (G : SimpleGraph α) [DecidableRel G.Adj]
    (hconn : G.Connected)
    (hmin : ∀ v, G.degree v ≥ d)
    (hfree : ∀ (f : Fin k ↪ α), ¬ ∀ i j, i ≠ j → G.Adj (f i) (f j)) :
    (sorry : ℕ) ≤ (sorry : ℕ) := by
  sorry

end Erdos612
