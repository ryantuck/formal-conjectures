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
# Erdős Problem 400

For $k \geq 2$, let $g_k(n)$ be the maximum of $(a_1 + \cdots + a_k) - n$ where
$a_1! \cdots a_k! \mid n!$.

Question 1: Is $\sum_{n \leq x} g_k(n) \sim c_k x \log x$ for some constant $c_k$?
Question 2: Is $g_k(n) = c_k \log x + o(\log x)$ for almost all $n < x$?

Erdős-Graham: $g_k(n) \ll_k \log n$ for all n.

*Reference:* [erdosproblems.com/400](https://www.erdosproblems.com/400)
-/

open Filter Topology BigOperators Real

namespace Erdos400

/-- g_k(n) is the maximum excess of sum over n for factorial divisibility -/
noncomputable def g (k n : ℕ) : ℤ :=
  sSup {m : ℤ | ∃ S : Finset ℕ, S.card = k ∧
    (S.prod Nat.factorial) ∣ n.factorial ∧ m = (S.sum (fun i => (i : ℤ))) - n}

/-- Erdős-Graham: g_k(n) is O_k(log n) -/
@[category research open, AMS 11]
theorem erdos_400_upper_bound :
    ∀ k : ℕ, k ≥ 2 → ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n > 0 →
      (g k n : ℝ) ≤ C * log n := by
  sorry

/-- Question 1: Sum asymptotic -/
def erdos_400_question1 (k : ℕ) : Prop :=
  ∃ c_k : ℝ, Tendsto (fun x => ((Finset.range x).sum (fun n => (g k n : ℝ))) / (x * log x))
    atTop (𝓝 c_k)

end Erdos400
