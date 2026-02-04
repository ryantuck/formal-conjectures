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
# Erdős Problem 235

*Reference:* [erdosproblems.com/235](https://www.erdosproblems.com/235)
-/

open Nat Filter Topology

namespace Erdos235

/--
Let $\{a_1<a_2<\cdots\}$ be the integers $<N_k$ which are relatively prime to $N_k$.
Then, for any $c\geq 0$, the limit
$\lim_{k\to\infty} \frac{\#\{ a_i-a_{i-1}\leq c \frac{N_k}{\phi(N_k)} : 2\leq i\leq \phi(N_k)\}}{\phi(N_k)}$
exists and is a continuous function of $c$.

Solved by Hooley [Ho65], who proved that these gaps have an exponential distribution.

[Ho65] Hooley, C., _On the difference of consecutive numbers prime to n_.
  Acta Arithmetica (1965), 343-347.
-/
@[category research solved, AMS 11]
theorem erdos_235 : ∀ c : ℝ, c ≥ 0 →
    ∃ f : ℝ → ℝ, ∃ N_k : ℕ → ℕ,
    Continuous f ∧
    (∀ k, ∃ primes : Finset ℕ, ∀ p ∈ primes, Nat.Prime p ∧ primes.card = k ∧ N_k k = primes.prod id) ∧
    Tendsto (fun k : ℕ =>
      let N := N_k k;
      let coprimes := (Finset.range N).filter (fun a => Nat.Coprime a N);
      let sorted := coprimes.sort (· ≤ ·);
      let gaps := sorted.zipWith (· - ·) sorted.tail;
      let threshold := c * (N : ℝ) / (N.totient : ℝ);
      ((gaps.filter (fun d => (d : ℝ) ≤ threshold)).length : ℝ) / (coprimes.card : ℝ)
    ) atTop (𝓝 (f c)) := by
  sorry

/--
Hooley proved that the distribution is $(1+o(1))(1-e^{-c})$.
-/
@[category research solved, AMS 11]
theorem erdos_235.hooley : ∃ o_fn : ℕ → ℝ, ∃ N_k : ℕ → ℕ,
    Tendsto o_fn atTop (𝓝 0) ∧
    (∀ k, ∃ primes : Finset ℕ, ∀ p ∈ primes, Nat.Prime p ∧ primes.card = k ∧ N_k k = primes.prod id) ∧
    ∀ c : ℝ, c ≥ 0 →
    Tendsto (fun k : ℕ =>
      let N := N_k k;
      let coprimes := (Finset.range N).filter (fun a => Nat.Coprime a N);
      let sorted := coprimes.sort (· ≤ ·);
      let gaps := sorted.zipWith (· - ·) sorted.tail;
      let threshold := c * (N : ℝ) / (N.totient : ℝ);
      ((gaps.filter (fun d => (d : ℝ) ≤ threshold)).length : ℝ) / (coprimes.card : ℝ)
    ) atTop (𝓝 (1 - Real.exp (-c))) := by
  sorry

end Erdos235
