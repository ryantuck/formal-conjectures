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
# Erdős Problem 322

Let $k \geq 3$ and $A \subset \mathbb{N}$ denote the set of $k$-th powers.
The problem investigates the order of growth of $1_A^{(k)}(n)$, which counts
representations of $n$ as a sum of $k$ many $k$-th powers.

Does there exist a constant $c > 0$ and infinitely many $n$ such that $1_A^{(k)}(n) > n^c$?

Mahler (1936) disproved Hardy-Littlewood Hypothesis K for k=3, showing $1_A^{(3)}(n) \gg n^{1/12}$.
Erdős-Chowla (1936): For all $k \geq 3$, $1_A^{(k)}(n) \gg n^{c/\log \log n}$ for infinitely many n.

*Reference:* [erdosproblems.com/322](https://www.erdosproblems.com/322)
-/

open Filter Topology BigOperators

namespace Erdos322

/-- Count of representations of n as sum of k many k-th powers -/
noncomputable def count_reps (k n : ℕ) : ℕ :=
  Nat.card {s : Finset ℕ | s.card = k ∧ s.sum (fun m => m^k) = n}

/-- Mahler (1936): For k=3, there are infinitely many n with Ω(n^(1/12)) representations -/
@[category research open, AMS 11]
theorem erdos_322_mahler_k3 :
    ∃ c : ℝ, c > 0 ∧ ∃ᶠ n in atTop, (count_reps 3 n : ℝ) ≥ c * (n : ℝ) ^ ((1:ℝ)/12) := by
  sorry

/-- Erdős-Chowla (1936): For all k ≥ 3, growth rate with log log factor -/
@[category research open, AMS 11]
theorem erdos_322_erdos_chowla (k : ℕ) (hk : k ≥ 3) :
    ∃ c : ℝ, c > 0 ∧ ∃ᶠ n in atTop,
      (count_reps k n : ℝ) ≥ (n : ℝ) ^ (c / Real.log (Real.log n)) := by
  sorry

/-- Central question: Does there exist c > 0 with infinitely many n having n^c reps? -/
def erdos_322_conjecture (k : ℕ) : Prop :=
  ∃ c : ℝ, c > 0 ∧ ∃ᶠ n in atTop, (count_reps k n : ℝ) > (n : ℝ) ^ c

end Erdos322
