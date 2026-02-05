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
# Erdős Problem 576

Determine the behavior of ex(n; Q_k), where Q_k is the k-dimensional hypercube graph.
Erdős conjectured ex(n; Q_3) ~ n^{8/5}.

OPEN

*Reference:* [erdosproblems.com/576](https://www.erdosproblems.com/576)
-/

open SimpleGraph Asymptotics

open scoped Topology Real

namespace Erdos576

variable {α : Type*}

/-- The Turán number ex(n; G): maximum edges avoiding G -/
noncomputable def extremalNumber (n : ℕ) (G : SimpleGraph α) : ℕ := sorry

/-- The k-dimensional hypercube graph with 2^k vertices -/
def hypercubeGraph (k : ℕ) : SimpleGraph (Fin (2^k)) := sorry

/-- Erdős' conjecture: ex(n; Q_3) ~ n^{8/5} -/
@[category research open, AMS 05]
theorem hypercube_three_conjecture (answer : Prop) :
    answer ↔ ∃ c : ℝ, c > 0 ∧
      (fun (n : ℕ) => (extremalNumber n (hypercubeGraph 3) : ℝ)) ~[Filter.atTop]
        (fun n => c * (n : ℝ) ^ (8 / 5)) := by
  sorry

/-- General problem: determine ex(n; Q_k) for all k -/
@[category research open, AMS 05]
theorem hypercube_extremal_behavior (k : ℕ) :
    ∃ f : ℕ → ℝ, ∀ᶠ (n : ℕ) in Filter.atTop,
      (extremalNumber n (hypercubeGraph k) : ℝ) ≤ f n := by
  sorry

end Erdos576
