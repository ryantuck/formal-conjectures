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
# Erdős Problem 548: Erdős-Sós Conjecture

Let n ≥ k+1. Every graph on n vertices with at least (k-1)n/2 + 1 edges contains
every tree on k+1 vertices.

OPEN

*Reference:* [erdosproblems.com/548](https://www.erdosproblems.com/548)
-/

namespace Erdos548

/-- Erdős-Sós conjecture on trees in dense graphs -/
@[category research open, AMS 05]
theorem erdos_sos_conjecture :
    ∀ (n k : ℕ), n ≥ k + 1 →
      ∀ (G : SimpleGraph (Fin n)),
        (Nat.card G.edgeSet ≥ ⌊(k - 1 : ℝ) * n / 2⌋₊ + 1) →
        ∀ {V : Type*} [Fintype V] (T : SimpleGraph V),
          T.IsTree → Fintype.card V = k + 1 →
          Nonempty (T ↪g G) := by
  sorry

end Erdos548
