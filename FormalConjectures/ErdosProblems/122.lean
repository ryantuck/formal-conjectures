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
# Erdős Problem 122

For which number theoretic functions $f$ is it true that, for any $F(n)$ satisfying
$f(n)/F(n) \to 0$ for almost all $n$, there exist infinitely many $x$ such that:
$$\frac{\#\{ n\in \mathbb{N} : n+f(n)\in (x,x+F(x))\}}{F(x)}\to \infty$$

Erdős, Pomerance, and Sárközy showed this holds for the divisor function $d(n)$ and
the count of distinct prime divisors $\omega(n)$. Erdős believed it is false when
$f(n) = \phi(n)$ (Euler's totient) or $\sigma(n)$ (sum of divisors).

*Reference:* [erdosproblems.com/122](https://www.erdosproblems.com/122)
-/

open Filter Topology

namespace Erdos122

/-- A property holds for almost all n if the exceptional set has density 0 -/
def AlmostAll (P : ℕ → Prop) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N,
    (Nat.card {k : ℕ | k < n ∧ ¬P k} : ℝ) < ε * n

/-- The shifted distribution property for arithmetic function f -/
def HasShiftedDistributionProperty (f : ℕ → ℕ) : Prop :=
  ∀ F : ℕ → ℝ,
    (∀ ε > 0, ∃ N, ∀ n ≥ N, (f n : ℝ) / F n < ε) →
    AlmostAll (fun n => (f n : ℝ) / F n < 1) →
    ∀ K : ℝ, ∃ X : ℕ, ∀ x ≥ X, ∃ M : ℕ, ∀ m ≥ M,
      (Nat.card {n : ℕ | n < m ∧ (x : ℝ) < (n : ℝ) + (f n : ℝ) ∧
        (n : ℝ) + (f n : ℝ) < (x : ℝ) + F x} : ℝ) / F x > K

/-- Erdős Problem 122: Characterize which arithmetic functions have the
    shifted distribution property.

    The problem asks: for which $f$ do we have this distribution property?
    This is an open research question. -/
def erdos_122 : Prop :=
  ∃ characterization : (ℕ → ℕ) → Prop,
    ∀ f : ℕ → ℕ, characterization f ↔ HasShiftedDistributionProperty f

end Erdos122
