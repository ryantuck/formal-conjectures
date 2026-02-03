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
import Mathlib.NumberTheory.ArithmeticFunction

/-!
# Erdős Problem 144

*Reference:* [erdosproblems.com/144](https://www.erdosproblems.com/144)
-/

namespace Erdos144

open Finset Filter Real Classical

/--
`n` has two divisors `d1, d2` such that `d1 < d2 < c * d1`.
-/
def HasCloseDivisors (n : ℕ) (c : ℝ) : Prop :=
  ∃ d1 d2, d1 ∣ n ∧ d2 ∣ n ∧ d1 < d2 ∧ (d2 : ℝ) < c * d1

/--
The set of integers satisfying `HasCloseDivisors n c`.
-/
def S (c : ℝ) : Set ℕ := { n | HasCloseDivisors n c }

/--
The natural density of a set `A` is `d`.
-/
def HasNaturalDensity (A : Set ℕ) (d : ℝ) : Prop :=
  Tendsto (fun N ↦ ((filter (· ∈ A) (Icc 1 N)).card : ℝ) / N) atTop (nhds d)

/--
Maier and Tenenbaum [MaTe84] proved that for any $c > 1$, the density of integers with
two divisors $d_1 < d_2 < c d_1$ is 1.
-/
@[category research solved, AMS 11]
theorem erdos_144 :
    ∀ c > 1, HasNaturalDensity (S c) 1 := by
  sorry

end Erdos144
