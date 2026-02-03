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
# Erdős Problem 161

*Reference:* [erdosproblems.com/161](https://www.erdosproblems.com/161)

Let $\alpha \in [0, 1/2)$ and $n, t \geq 1$. Let $F^{(t)}(n,\alpha)$ be the smallest $m$ such that 
we can 2-colour the edges of the complete $t$-uniform hypergraph on $n$ vertices such that 
if $X \subseteq [n]$ with $|X| \geq m$, then there are at least $\alpha \binom{|X|}{t}$ 
many $t$-subsets of $X$ of each colour.

For fixed $n, t$, as we change $\alpha$ from $0$ to $1/2$, does $F^{(t)}(n,\alpha)$ 
increase continuously or are there jumps? Only one jump?
-/

open Finset

namespace Erdos161

/--
$F^{(t)}(n,\alpha)$ is the smallest $m$ such that we can 2-colour the edges of the 
complete $t$-uniform hypergraph on $n$ vertices such that if $X \subseteq [n]$ 
with $|X| \geq m$, then there are at least $\alpha \binom{|X|}{t}$ many $t$-subsets 
of $X$ of each colour.
-/
noncomputable def erdos_161.F (t n : ℕ) (α : ℝ) : ℕ :=
  sInf { m | ∃ (f : (powersetCard t (univ : Finset (Fin n))) → Fin 2),
    ∀ (X : Finset (Fin n)), m ≤ X.card →
      (α * (X.card.choose t) : ℝ) ≤ ((powersetCard t X).attach.filter (λ e => f ⟨e.1, powersetCard_mono (subset_univ X) e.2⟩ = 0)).card ∧
      (α * (X.card.choose t) : ℝ) ≤ ((powersetCard t X).attach.filter (λ e => f ⟨e.1, powersetCard_mono (subset_univ X) e.2⟩ = 1)).card }

/--
Erdős's guess was that "the jump occurs all in one step at 0". 
This can be interpreted as saying that for any $\alpha_1, \alpha_2 \in (0, 1/2)$, 
the growth rates of $F^{(t)}(n, \alpha_1)$ and $F^{(t)}(n, \alpha_2)$ are the same, 
while they differ from the growth rate of $F^{(t)}(n, 0)$.
-/
@[category research open, AMS 5]
theorem erdos_161.one_jump :
  ∀ (t : ℕ), 2 ≤ t →
    ∀ (α1 α2 : ℝ), 0 < α1 → α1 < 1/2 → 0 < α2 → α2 < 1/2 →
      (fun n => (erdos_161.F t n α1 : ℝ)) =Θ[Filter.atTop] (fun n => (erdos_161.F t n α2 : ℝ)) :=
  sorry

/--
The jump at 0: for any $\alpha > 0$, the growth rate of $F^{(t)}(n, \alpha)$ is different 
from that of $F^{(t)}(n, 0)$.
Specifically, $F^{(t)}(n, 0) \asymp \log_{t-1} n$.
-/
@[category research open, AMS 5]
theorem erdos_161.jump_at_zero :
  ∀ (t : ℕ), 2 ≤ t →
    ∀ (α : ℝ), 0 < α → α < 1/2 →
      ¬((fun n => (erdos_161.F t n α : ℝ)) =Θ[Filter.atTop] (fun n => (erdos_161.F t n 0 : ℝ))) :=
  sorry

end Erdos161
