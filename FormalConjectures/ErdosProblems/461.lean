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
# Erdős Problem 461

Let s_t(n) denote the t-smooth component of n—the product of all prime factors p
(with multiplicity) of n where p < t. Define f(n,t) as the count of distinct values
of s_t(m) for m ∈ [n+1, n+t].

Is it true that f(n,t) ≫ t uniformly for all t and n?

Erdős-Graham: f(n,t) ≫ t/log t.

*Reference:* [erdosproblems.com/461](https://www.erdosproblems.com/461)
-/

open Filter Topology BigOperators Real Classical

namespace Erdos461

/-- s_t(n) is the t-smooth component -/
noncomputable def s_t (t n : ℕ) : ℕ :=
  (n.primeFactorsList.filter (· < t)).prod

/-- f(n,t) counts distinct smooth components in interval -/
noncomputable def f (n t : ℕ) : ℕ :=
  Nat.card {s : ℕ | ∃ m : ℕ, n < m ∧ m ≤ n + t ∧ s_t t m = s}

/-- Erdős-Graham: Lower bound -/
@[category research open, AMS 11]
theorem erdos_461_lower :
    ∃ c : ℝ, c > 0 ∧ ∀ n t : ℕ, t ≥ 2 →
      (f n t : ℝ) ≥ c * t / log t := by
  sorry

/-- Conjecture: Linear lower bound -/
@[category research open, AMS 11]
theorem erdos_461_conjecture :
    ∃ c : ℝ, c > 0 ∧ ∀ n t : ℕ, (f n t : ℝ) ≥ c * t := by
  sorry

end Erdos461
