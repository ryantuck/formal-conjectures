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
# Erdős Problem 962

Maximal k in divisibility sequence.

OPEN

*Reference:* [erdosproblems.com/962](https://www.erdosproblems.com/962)
-/

open Finset Filter

open scoped Topology Real

namespace Erdos962

/-- Maximal length of consecutive integers divisible by large primes -/
noncomputable def k (n : ℕ) : ℕ := sorry

/-- Estimate for k(n) -/
@[category research open, AMS 11]
theorem divisibility_sequence_length (answer : Prop) :
    answer ↔ ∃ (f : ℕ → ℝ),
      Tendsto (fun n => (k n : ℝ) / f n) atTop (nhds 1) := by
  sorry

end Erdos962
