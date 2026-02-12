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

namespace Erdos1074

/-!
# Erdős Problem 1074

STATUS: SOLVED

*Reference:* [erdosproblems.com/1074](https://www.erdosproblems.com/1074)
-/

open scoped Nat

/--
English version:  The EHS numbers (after Erdős, Hardy, and Subbarao) are those $m\geq 1$ such that there
exists a prime $p\not\equiv 1\pmod{m}$ such that $m! + 1 \equiv 0\pmod{p}$. -/
abbrev Nat.EHSNumbers : Set ℕ := {m | 1 ≤ m ∧ ∃ p, p.Prime ∧ ¬p ≡ 1 [MOD m] ∧ p ∣ m ! + 1}

/--
English version: The Pillai primes are those primes $p$ such that there exists an $m$ with
$p\not\equiv 1\pmod{m}$ such that $m! + 1 \equiv 0\pmod{p}$. -/
def PillaiPrimes : Set ℕ := {p | p.Prime ∧ ∃ m, 1 ≤ m ∧ ¬p ≡ 1 [MOD m] ∧ p ∣ m ! + 1}

/--
English version:  -/
@[category research open, AMS 11]
theorem erdos_1074.part8_i_i : answer(sorry) ↔ ∃ c, Set.HasDensity Nat.EHSNumbers c := by
  sorry

/--
English version:  Let $S$ be the set of all $m\geq 1$ such that there exists a prime $p\not\equiv 1\pmod{m}$ such
that $m! + 1 \equiv 0\pmod{p}$. What is
$$
  \lim\frac{|S\cap[1, x]|}{x}?
$$ -/@[category research open, AMS 11]
theorem erdos_1074.part_i_ii : Set.HasDensity Nat.EHSNumbers answer(sorry) := by
  sorry

/--
English version:  Similarly, if $P$ is the set of all primes $p$ such that there exists an $m$ with
$p\not\equiv 1\pmod{m}$ such that $m! + 1 \equiv 0\pmod{p}$, then does
$$
  \lim\frac{|P\cap[1, x]|}{\pi(x)}
$$
exist? -/@[category research open, AMS 11]
theorem erdos_1074.part_ii_i : answer(sorry) ↔ ∃ c, Set.HasDensity PillaiPrimes c {p | p.Prime} := by
  sorry

/--
English version:  Similarly, if $P$ is the set of all primes $p$ such that there exists an $m$ with
$p\not\equiv 1\pmod{m}$ such that $m! + 1 \equiv 0\pmod{p}$, then what is
$$
  \lim\frac{|P\cap[1, x]|}{\pi(x)}?
$$ -/@[category research open, AMS 11]
theorem erdos_1074.parts_ii_ii :
    Set.HasDensity PillaiPrimes answer(sorry) {p | p.Prime} := by
  sorry

/--
English version:  Pillai [Pi30] raised the question of whether there exist any primes in $P$. This was answered
by Chowla, who noted that, for example, $14! + 1 \equiv 18! + 1 \equiv 0 \pmod{23}$. -/@[category test, AMS 11]
theorem erdos_1074.variants.mem_pillaiPrimes : 23 ∈ PillaiPrimes := by
  simp [PillaiPrimes]
  refine ⟨by norm_num, 14, by norm_num, by decide, by norm_num⟩

/-- English version: Erdős, Hardy, and Subbarao proved that $S$ is infinite. -/@[category research solved, AMS 11]
theorem erdos_1074.variants.EHSNumbers_infinite : Nat.EHSNumbers.Infinite := by
  sorry

/-- English version: Erdős, Hardy, and Subbarao proved that $P$ is infinite. -/@[category research solved, AMS 11]
theorem erdos_1074.variants.PillaiPrimes_infinite : PillaiPrimes.Infinite := by
  sorry

/-- English version: The sequence $S$ begins $8, 9, 13, 14, 15, 16, 17, ...$ -/@[category test, AMS 11]
theorem erdos_1074.variants.EHSNumbers_init :
    Nat.nth Nat.EHSNumbers '' (Set.Icc 0 6) = {8, 9, 13, 14, 15, 16, 17} := by
  sorry

/-- English version: The sequence $P$ begins $23, 29, 59, 61, 67, 71, ...$ -/@[category test, AMS 11]
theorem erdos_1074.variants.PillaiPrimes_init :
    Nat.nth PillaiPrimes '' (Set.Icc 0 5) = {23, 29, 59, 61, 67, 71} := by
  sorry

/--
English version:  Regarding the first question, Hardy and Subbarao computed all EHS numbers up to $2^{10}$, and
write "...if this trend conditions we expect [the limit] to be around 0.5, if it exists." -/@[category research open, AMS 11]
theorem erdos_1074.variants.EHSNumbers_one_half : Set.HasDensity Nat.EHSNumbers (1 / 2) := by
  sorry

end Erdos1074
