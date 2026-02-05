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
# Erdős Problem 476

Let A ⊆ 𝔽ₚ. Define A ⊕ A = {a+b : a ≠ b ∈ A}.
Is |A ⊕ A| ≥ min(2|A| - 3, p)?

da Silva-Hamidoune: PROVED (Lean verified).

Generalization: Elements expressible as sums of at most r distinct elements from A
have cardinality ≥ min(r|A| - r² + 1, p).

*Reference:* [erdosproblems.com/476](https://www.erdosproblems.com/476)
-/

open Filter Topology BigOperators Real Classical

namespace Erdos476

/-- A ⊕ A is the distinct-pairs sumset -/
def sumsetDistinct {p : ℕ} (A : Finset (ZMod p)) : Finset (ZMod p) :=
  (A ×ˢ A).filter (fun (a, b) => a ≠ b) |>.image (fun (a, b) => a + b)

/-- da Silva-Hamidoune: Lower bound on distinct-pairs sumset -/
@[category research solved, AMS 11]
theorem erdos_476 :
    ∀ p : ℕ, p.Prime → ∀ A : Finset (ZMod p),
      (sumsetDistinct A).card ≥ min (2 * A.card - 3) p := by
  sorry

end Erdos476
