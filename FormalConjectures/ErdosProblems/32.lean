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

import Mathlib.NumberTheory.Harmonic.EulerMascheroni



/-!

# Erdős Problem 32



*Reference:* [erdosproblems.com/32](https://www.erdosproblems.com/32)

-/



namespace Erdos32



open scoped BigOperators



/--

A set `A` is an additive complement to the primes if every sufficiently large integer can be written

as `p + a` for some prime `p` and `a ∈ A`.

-/

def IsPrimeComplement (A : Set ℕ) : Prop :=

  ∀ᶠ n in Filter.atTop, ∃ p a, p.Prime ∧ a ∈ A ∧ p + a = n



/--

Is there a set $A \subseteq \mathbb{N}$ such that $|A \cap \{1, \dots, N\}| = o((\log N)^2)$ and

$A$ is an additive complement to the primes?



Can the bound $O(\log N)$ be achieved?



Must such an $A$ satisfy $\liminf \frac{|A \cap \{1, \dots, N\}|}{\log N} > 1$?



The answers are:

1. Yes, $O((\log N)^2)$ is possible (Erdős [Er54]).

2. Yes, $O(\log N)$ is possible (Ruzsa [Ru98c]).

3. Yes, liminf > 1 is necessary (Ruzsa [Ru98c] proved liminf >= e^gamma approx 1.781).



[Er54] P. Erdős, _Some problems on the distribution of prime numbers_, Teubner, Leipzig, 1954.

[Ru98c] I. Z. Ruzsa, _On the additive completion of primes_, Acta Arith. 86 (1998), 269–275.

-/

@[category research solved, AMS 11]

theorem erdos_32 : answer(True) ↔ ∃ A : Set ℕ, IsPrimeComplement A ∧

    (fun n ↦ ((A ∩ {x | x ≤ n}).ncard : ℝ)) =O[Filter.atTop] (fun n ↦ Real.log n) := by

  sorry



/--

Must such an $A$ satisfy $\liminf \frac{|A \cap \{1, \dots, N\}|}{\log N} > 1$?



The answer is yes: Ruzsa [Ru98c] proved that we must have

$ \liminf_{N \to \infty} \frac{|A \cap \{1, \dots, N\}|}{\log N} \geq e^\gamma. $

-/

@[category research solved, AMS 11]

theorem erdos_32.variants.liminf : ∀ A : Set ℕ, IsPrimeComplement A →

    Real.exp Real.eulerMascheroniConstant ≤ Filter.atTop.liminf (fun n ↦ (A ∩ {x | x ≤ n}).ncard / Real.log n) := by

  sorry



end Erdos32
