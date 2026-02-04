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
# Erdős Problem 237

*Reference:* [erdosproblems.com/237](https://www.erdosproblems.com/237)
-/

open Filter Topology

namespace Erdos237

/--
The number of solutions to $n=p+a$ for $p$ prime and $a\in A$.
-/
noncomputable def f (A : Set ℕ) [DecidablePred (· ∈ A)] (n : ℕ) : ℕ :=
  (Finset.range n).filter (fun k => Nat.Prime k ∧ n - k ∈ A) |>.card

/--
Let $A\subseteq \mathbb{N}$ be a set such that $\lvert A\cap \{1,\ldots,N\}\rvert \gg \log N$
for all large $N$. Let $f(n)$ count the number of solutions to $n=p+a$ for $p$ prime
and $a\in A$. Is it true that $\limsup f(n)=\infty$?

The answer is yes, as proved by Chen and Ding [ChDi22] - in fact, the assumption
that $A$ grows like $\log N$ can be replaced just with the assumption that $A$ is infinite.

[ChDi22] Chen, Y.-G. and Ding, S., _On a problem of Erdős about integers of the form $p+a$_.
  Proceedings of the Edinburgh Mathematical Society (2022), 491-496.
-/
@[category research solved, AMS 11]
theorem erdos_237 : ∀ A : Set ℕ, ∀ _inst : DecidablePred (· ∈ A),
    Set.Infinite A →
    ¬ BddAbove (Set.range (f A)) := by
  sorry

/--
Chen and Ding's result: if $A$ is infinite, then $\limsup f(n)=\infty$.
-/
@[category research solved, AMS 11]
theorem erdos_237.chen_ding : ∀ A : Set ℕ, ∀ _inst : DecidablePred (· ∈ A),
    Set.Infinite A →
    Tendsto (fun N => ⨆ n ≤ N, (f A n : ℝ)) atTop atTop := by
  sorry

end Erdos237
