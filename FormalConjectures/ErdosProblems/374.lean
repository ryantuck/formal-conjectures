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
# Erdős Problem 374

For $m \in \mathbb{N}$, let $F(m)$ be the minimal $k \geq 2$ such that there exist
$a_1 < \cdots < a_k = m$ where $a_1! \cdots a_k!$ is a perfect square.
Let $D_k = \{m : F(m) = k\}$.

What is the growth rate of $|D_k \cap \{1,\ldots,n\}|$ for $3 \leq k \leq 6$?
In particular, does $|D_6 \cap \{1,\ldots,n\}| \gg n$?

Known: $D_2 = \{n^2 : n > 1\}$, $D_k = \emptyset$ for k > 6, smallest element in $D_6$ is 527.

*Reference:* [erdosproblems.com/374](https://www.erdosproblems.com/374)
-/

open Filter Topology BigOperators

namespace Erdos374

/-- F(m) is the minimal k such that m is largest in a k-tuple with square product -/
noncomputable def F (m : ℕ) : ℕ :=
  sInf {k : ℕ | k ≥ 2 ∧ ∃ seq : Finset ℕ,
    seq.card = k ∧ seq.max' (by sorry) = m ∧
    ∃ r : ℕ, (seq.prod Nat.factorial) = r^2}

/-- D_k is the set of m with F(m) = k -/
def D (k : ℕ) : Set ℕ :=
  {m : ℕ | F m = k}

/-- D_2 consists exactly of perfect squares > 1 -/
@[category research open, AMS 11]
theorem erdos_374_D2 : D 2 = {m : ℕ | ∃ n > 1, m = n^2} := by
  sorry

/-- D_k is empty for k > 6 -/
@[category research open, AMS 11]
theorem erdos_374_D_empty : ∀ k > 6, D k = ∅ := by
  sorry

/-- Question: Does D_6 have linear density? -/
def erdos_374_conjecture : Prop :=
  ∃ c : ℝ, c > 0 ∧ ∀ᶠ n : ℕ in atTop,
    (Nat.card {m ∈ D 6 | m ≤ n} : ℝ) ≥ c * n

end Erdos374
