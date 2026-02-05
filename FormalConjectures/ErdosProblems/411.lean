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
# Erdős Problem 411

Let $g(n) = n + \phi(n)$ and $g_k(n) = g^k(n)$ (k-fold iteration).
For which $(n,r)$ does $g_{k+r}(n) = 2g_k(n)$ hold for all large k?

Known: (n,r) = (10,2), (94,2) work. Selfridge-Weintraub found $g_{k+9}(n) = 9g_k(n)$ cases.
Steinerberger & Cambie: For r=2, solutions have restricted odd part structure.

*Reference:* [erdosproblems.com/411](https://www.erdosproblems.com/411)
-/

open Filter Topology BigOperators

namespace Erdos411

/-- g(n) = n + φ(n) -/
def g (n : ℕ) : ℕ := n + Nat.totient n

/-- k-fold iteration of g -/
def g_iter : ℕ → ℕ → ℕ
  | 0, n => n
  | k+1, n => g (g_iter k n)

/-- Periodic doubling property -/
def HasPeriodicDoubling (n r : ℕ) : Prop :=
  ∃ K : ℕ, ∀ k ≥ K, g_iter (k + r) n = 2 * g_iter k n

/-- Known solutions: (10,2) and (94,2) -/
@[category research open, AMS 11]
theorem erdos_411_known_solutions :
    HasPeriodicDoubling 10 2 ∧ HasPeriodicDoubling 94 2 := by
  sorry

end Erdos411
