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
# Erdős Problem 401

Does there exist f(r) → ∞ such that for infinitely many n, we can find $a_1, a_2$ with
$a_1 + a_2 > n + f(r) \log n$ where $a_1! \cdot a_2! \mid n! \cdot 2^n \cdot 3^n \cdots p_r^n$?

PROVED by Barreto-Leeham using construction from problem 729.

*Reference:* [erdosproblems.com/401](https://www.erdosproblems.com/401)
-/

open Filter Topology BigOperators Real

namespace Erdos401

/-- Barreto-Leeham: Affirmative solution -/
@[category research solved, AMS 11]
theorem erdos_401 :
    ∃ f : ℕ → ℝ, (Tendsto f atTop atTop) ∧
      ∀ r : ℕ, ∃ᶠ n : ℕ in atTop, ∃ a₁ a₂ : ℕ,
        (a₁ + a₂ : ℝ) > n + f r * log n ∧
        ∃ primes : Finset ℕ, primes.card = r ∧ (∀ p ∈ primes, p.Prime) ∧
        (a₁.factorial * a₂.factorial) ∣ (n.factorial * primes.prod (fun p => p ^ n)) := by
  sorry

end Erdos401
