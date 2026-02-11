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
# Erdős Problem 1157

Turán numbers for r-uniform hypergraphs.

OPEN

*Reference:* [erdosproblems.com/1157](https://www.erdosproblems.com/1157)
-/

open Finset Filter Asymptotics

open scoped Topology Real

namespace Erdos1157

variable {α : Type*}

/-- Brown-Erdős-Sós Conjecture: For all r > t ≥ 2 and s ≥ 3,
    ex_t(n, F) = o(n^t) whenever k ≥ (r-t)s + t + 1,
    where F is the family of all r-uniform hypergraphs with k vertices and s edges.

    This formalization captures the asymptotic growth condition. The full statement
    would require formal definitions of uniform hypergraphs and extremal numbers. -/
@[category research open, AMS 05]
theorem brown_erdos_sos_conjecture :
    ∀ (r t s k : ℕ), r > t → t ≥ 2 → s ≥ 3 → k ≥ (r - t) * s + t + 1 →
    ∃ (ex : ℕ → ℕ), (fun n => (ex n : ℝ)) =o[atTop] (fun n => (n : ℝ)^t) := by
  sorry

/-- Known lower bound: For all k > r and s > 1,
    ex_r(n, F) ≫ n^((rs-k)/(s-1)) where F is the family of r-uniform hypergraphs
    with k vertices and s edges. (Brown, Erdős, Sós) -/
@[category research open, AMS 05]
theorem turan_hypergraph_lower_bound :
    ∀ (r k s : ℕ), k > r → s > 1 →
    ∃ (C : ℝ) (N : ℕ), C > 0 ∧ ∀ n ≥ N,
      ∃ (ex : ℕ → ℕ), (ex n : ℝ) ≥ C * (n : ℝ)^(((r * s - k : ℤ) : ℝ) / ((s - 1) : ℝ)) := by
  sorry

end Erdos1157
