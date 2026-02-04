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

/-!
# Erdős Problem 176

*Reference:* [erdosproblems.com/176](https://www.erdosproblems.com/176)

Let $N(k,\ell)$ be the minimal $N$ such that for any $f:\{1,\dots,N\}	o\{-1,1\}$ there must exist
a $k$-term arithmetic progression $P$ such that
$$ \left\lvert \sum_{n\in P}f(n)ightvert \geq \ell. $$
-/

namespace Erdos176

open Finset

/--
A set is a $k$-term arithmetic progression if it is of the form $\{a, a+d, \dots, a+(k-1)d\}$
for some $a$ and $d > 0$.
-/
def IsAP (P : Finset ℕ) (k : ℕ) : Prop :=
  ∃ (a d : ℕ), d > 0 ∧ P = Finset.image (fun i => a + i * d) (Finset.range k)

/--
$N(k, \ell)$ is the minimal $N$ such that any $\{-1, 1\}$-colouring of $\{1, \dots, N\}$
contains a $k$-term AP with discrepancy at least $\ell$.
-/
noncomputable def N (k : ℕ) (ℓ : ℝ) : ℕ :=
  sInf { n : ℕ | ∀ (f : ℕ → ℤ), (∀ i ∈ Icc 1 n, f i = 1 ∨ f i = -1) →
    ∃ (P : Finset ℕ), P ⊆ Icc 1 n ∧ IsAP P k ∧ |∑ i ∈ P, f i| ≥ ℓ }

/--
Is it true that for any $c > 0$ there exists some $C > 1$ such that $N(k, ck) \leq C^k$?
-/
@[category research open, AMS 05 11]
theorem erdos_176_1 :
    ∀ (c : ℝ), c > 0 → ∃ (C : ℝ), C > 1 ∧ ∀ (k : ℕ), (k : ℝ) ≥ 1 → (N k (c * k) : ℝ) ≤ C ^ k := by
  sorry

/--
Is it true that $N(k, 2) \leq C^k$ for some $C > 1$?
-/
@[category research open, AMS 05 11]
theorem erdos_176_2 :
    ∃ (C : ℝ), C > 1 ∧ ∀ (k : ℕ), (k : ℝ) ≥ 1 → (N k 2 : ℝ) ≤ C ^ k := by
  sorry

/--
Is it true that $N(k, \sqrt{k}) \leq C^k$ for some $C > 1$?
-/
@[category research open, AMS 05 11]
theorem erdos_176_3 :
    ∃ (C : ℝ), C > 1 ∧ ∀ (k : ℕ), (k : ℝ) ≥ 1 → (N k (Real.sqrt k) : ℝ) ≤ C ^ k := by
  sorry

end Erdos176
