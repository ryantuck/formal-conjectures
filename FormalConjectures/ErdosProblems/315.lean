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
# Erdős Problem 315

Define the sequence $u_1 = 1$ and $u_{n+1} = u_n(u_n + 1)$, which satisfies
$u_k = \lfloor c_0^{2^k} + 1 \rfloor$ for $k \geq 1$ where
$c_0 = \lim u_n^{1/2^n} = 1.264085\cdots$ (the Vardi constant).

For any other sequence $a_1 < a_2 < \cdots$ satisfying $\sum \frac{1}{a_k} = 1$,
must it be true that $\liminf a_n^{1/2^n} < c_0$?

Kamio (2025) and Li-Tang (2025) independently proved this, verified in Lean.

*Reference:* [erdosproblems.com/315](https://www.erdosproblems.com/315)
-/

open Filter Topology BigOperators Real

namespace Erdos315

/-- The Vardi sequence: u₁ = 1, u_{n+1} = u_n(u_n + 1) -/
def vardi_seq : ℕ → ℕ
  | 0 => 1
  | n + 1 => vardi_seq n * (vardi_seq n + 1)

/-- The Vardi constant c₀ ≈ 1.264085 -/
noncomputable def c₀ : ℝ :=
  limUnder atTop (fun n => ((vardi_seq n : ℝ) ^ (1 / 2^n)))

/-- For any increasing sequence summing to 1, liminf a_n^(1/2^n) < c₀ -/
@[category research solved, AMS 11]
theorem erdos_315_vardi_minimal (a : ℕ → ℕ) :
    StrictMono a →
    (∑' n, (1 : ℝ) / a n) = 1 →
    Filter.liminf (fun n => ((a n : ℝ) ^ (1 / 2^n))) atTop < c₀ := by
  sorry

end Erdos315
