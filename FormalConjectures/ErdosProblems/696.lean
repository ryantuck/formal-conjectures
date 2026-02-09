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
# Erdős Problem 696

Estimate h(n) and H(n) for prime/divisor sequences with p_{i+1} ≡ 1 (mod p_i).

OPEN

*Reference:* [erdosproblems.com/696](https://www.erdosproblems.com/696)
-/

open Nat Filter Asymptotics

open scoped Topology Real

namespace Erdos696

/-- h(n): minimal length of sequence where p_{i+1} ≡ 1 (mod p_i) -/
noncomputable def h (n : ℕ) : ℕ := sorry

/-- H(n): maximal length of sequence where p_{i+1} ≡ 1 (mod p_i) -/
noncomputable def H (n : ℕ) : ℕ := sorry

/-- Bounds for h(n) and H(n) -/
@[category research open, AMS 11]
theorem prime_sequence_congruence_bounds :
    ∃ f g : ℕ → ℕ,
      (fun n => (h n : ℝ)) ~[atTop] (fun n => (f n : ℝ)) ∧
      (fun n => (H n : ℝ)) ~[atTop] (fun n => (g n : ℝ)) := by
  sorry

end Erdos696
