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
# Erdős Problem 162

*Reference:* [erdosproblems.com/162](https://www.erdosproblems.com/162)

Let `α > 0` and `n ≥ 1`. Let `F(n, α)` be the smallest `k` such that there exists some
2-colouring of the edges of `Kₙ` in which any induced subgraph `H` on at least `k`
vertices contains more than `α * (Nat.choose (Fintype.card H) 2)` edges of each colour.

**Conjecture:** For every fixed `0 ≤ α ≤ 1/2`, as `n → ∞`,
`F(n, α) ~ c * log n` for some constant `c`.

Note: The original problem statement on erdosproblems.com uses "largest k", but this
is likely a typo for "smallest k" given the asymptotic behavior `c * log n`.
If `k` satisfies the condition, then any `k' > k` also satisfies it, so the set of
such `k` is $\{k_{min}, \dots, n\}$.
-/

namespace Erdos162

open Filter Real SimpleGraph

/--
The property that a 2-edge-colouring of a complete graph on `n` vertices
has the property that any induced subgraph on at least `k` vertices has
at least `α` proportion of edges of each colour.
-/
def Erdmulticolor (n k : ℕ) (α : ℝ) (c : Sym2 (Fin n) → Fin 2) : Prop :=
  ∀ (V' : Finset (Fin n)),
    k ≤ V'.card →
    let G := completeGraph (Fin n)
    let induced_edges := G.edgeFinset.filter (fun e => ∀ x ∈ e, x ∈ V')
    ∀ i : Fin 2, α * (V'.card.choose 2 : ℝ) < (induced_edges.filter (fun e => c e = i)).card

/--
`F(n, α)` is the smallest `k` such that there exists a 2-colouring of the edges of `Kₙ`
such that any induced subgraph `H` on at least `k` vertices has more than
`α * (Nat.choose (Fintype.card H) 2)` edges of each colour.
-/
noncomputable def F (n : ℕ) (α : ℝ) : ℕ :=
  sInf { k | ∃ (c : Sym2 (Fin n) → Fin 2), Erdmulticolor n k α c }

/--
The conjecture that `F(n, α)` is asymptotically `c * log n` for some constant `c`.
-/
@[category research open, AMS 05]
theorem erdos_162 (α : ℝ) (hα : 0 ≤ α ∧ α ≤ 1/2) :
    ∃ (c : ℝ), Tendsto (fun n => (F n α : ℝ) / (c * log n)) atTop (nhds 1) := by
  sorry

end Erdos162