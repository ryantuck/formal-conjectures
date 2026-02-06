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
# Erdős Problem 895

Triangle-free graph has independent a, b, a+b.

PROVED

*Reference:* [erdosproblems.com/895](https://www.erdosproblems.com/895)
-/

open Finset

open scoped Topology Real

namespace Erdos895

/-- Triangle-free graph on {1,...,n} has independent sum -/
@[category research solved, AMS 05]
theorem triangle_free_independent_sum (n : ℕ) :
    ∀ (G : SimpleGraph (Fin n)),
      G.CliqueFree 3 →
      ∃ (a b : Fin n), ¬G.Adj a b ∧
        ∃ (c : Fin n), c.val = a.val + b.val ∧
          ¬G.Adj a c ∧ ¬G.Adj b c := by
  sorry

end Erdos895
