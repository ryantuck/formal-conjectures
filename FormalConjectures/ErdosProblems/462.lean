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
# Erdős Problem 462

Let p(n) denote the least prime factor of n. A constant c > 0 exists such that:
  ∑_{n<x, n not prime} p(n)/n ~ c·x^(1/2)/(log x)²

Does there exist C > 0 such that for all large x:
  ∑_{x ≤ n ≤ x+C·x^(1/2)·(log x)²} p(n)/n ≫ 1 ?

*Reference:* [erdosproblems.com/462](https://www.erdosproblems.com/462)
-/

open Filter Topology BigOperators Real Classical

namespace Erdos462

/-- p(n) is the least prime factor -/
noncomputable def p (n : ℕ) : ℕ :=
  n.minFac

/-- Global asymptotic formula -/
@[category research open, AMS 11]
theorem erdos_462_global :
    ∃ c : ℝ, c > 0 ∧
      Tendsto (fun x : ℕ =>
        ((Finset.range x).filter (fun n => ¬n.Prime ∧ n > 1)).sum (fun n => (p n : ℝ) / n) /
        (x ^ ((1:ℝ)/2) / (log x)^2)) atTop (𝓝 c) := by
  sorry

/-- Short interval question -/
@[category research open, AMS 11]
theorem erdos_462_short_interval :
    ∃ C c : ℝ, C > 0 ∧ c > 0 ∧ ∀ᶠ x : ℕ in atTop,
      let interval := Finset.Ico x ⌊x + C * x ^ ((1:ℝ)/2) * (log x)^2⌋₊
      c ≤ interval.sum (fun n => (p n : ℝ) / n) := by
  sorry

end Erdos462
