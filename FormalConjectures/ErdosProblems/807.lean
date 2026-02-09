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
# Erdős Problem 807

Random graph bipartition number.

DISPROVED

*Reference:* [erdosproblems.com/807](https://www.erdosproblems.com/807)
-/

open Finset

open scoped Topology Real

namespace Erdos807

variable {α : Type*}

/-- Bipartition number -/
noncomputable def bipartitionNumber (G : SimpleGraph α) : ℕ := sorry

/-- Independence number -/
noncomputable def independenceNumber (G : SimpleGraph α) : ℕ := sorry

/-- Disproved: τ(G) = n - α(G) almost surely -/
@[category research solved, AMS 05]
theorem not_random_bipartition :
    ¬ ∀ (n : ℕ), ∀ᶠ (G : SimpleGraph (Fin n)) in Filter.atTop,
      bipartitionNumber G = n - independenceNumber G := by
  sorry

end Erdos807
