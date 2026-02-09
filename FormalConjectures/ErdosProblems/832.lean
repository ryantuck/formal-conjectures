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
# Erdős Problem 832

Hypergraph chromatic number edge bound.

DISPROVED

*Reference:* [erdosproblems.com/832](https://www.erdosproblems.com/832)
-/

open Finset

open scoped Topology Real

namespace Erdos832

variable {α : Type*}

/-- Chromatic number -/
noncomputable def chromaticNumber (H : Finset (Finset α)) : ℕ := sorry

/-- Disproved edge bound for chromatic k -/
@[category research solved, AMS 05]
theorem not_hypergraph_chromatic_edge_bound (r k : ℕ) (hr : r ≥ 3) :
    ¬ ∀ (H : Finset (Finset α)),
      (∀ e ∈ H, e.card = r) →
      chromaticNumber H = k →
      H.card ≥ Nat.choose ((r - 1) * (k - 1) + 1) r := by
  sorry

end Erdos832
