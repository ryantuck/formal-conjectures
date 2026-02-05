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
# Erdős Problem 543

Define f(N) as the minimal k such that: if G is an abelian group of size N and A ⊆ G
is a random set of size k, then with probability ≥ 1/2, every element of G can be
expressed as ∑_{x∈S} x for some S ⊆ A.

Is f(N) ≤ log₂ N + o(log log N)?

DISPROVED: ChatGPT-Tang disproved the conjecture, confirming Erdős' intuition.

*Reference:* [erdosproblems.com/543](https://www.erdosproblems.com/543)
-/

open MeasureTheory ProbabilityTheory Real

namespace Erdos543

variable {G : Type*} [AddCommGroup G] [Fintype G] [MeasurableSpace G]

/-- Upper bound by Erdős-Rényi -/
@[category research solved, AMS 11 60]
theorem erdos_renyi_bound :
    ∃ C : ℝ, C > 0 ∧ sorry := by
  sorry

/-- Disproof: improvement to o(log log N) is impossible -/
@[category research solved, AMS 11 60]
theorem no_improvement_to_o_loglogN :
    answer(False) ↔ sorry := by
  sorry

end Erdos543
