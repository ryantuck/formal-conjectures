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
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Sym.Sym2

/-!
# Erdős Problem 129

*Reference:* [erdosproblems.com/129](https://www.erdosproblems.com/129)
-/

namespace Erdos129

open SimpleGraph Finset Real Classical Sym2

/--
`ContainsKk G S k` means the subgraph of `G` induced by `S` contains a $K_k$.
-/
def ContainsKk {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (S : Finset V) (k : ℕ) : Prop :=
  ∃ K ⊆ S, G.IsClique (K : Set V) ∧ K.card = k

/--
`Prop129 N n k r` holds if for every `r`-coloring of `K_N`, there exists a subset of size `n`
which does not contain a monochromatic $K_k$ in at least one color.
Wait, the problem says "does not contain a copy of $K_k$ in at least one of the $r$ colours".
This means $\exists c, \neg (\text{contains } K_k \text{ in color } c)$.
-/
def Prop129 (N n k r : ℕ) : Prop :=
  ∀ (χ : Sym2 (Fin N) → Fin r),
    ∃ S : Finset (Fin N), S.card = n ∧
      ∃ c : Fin r,
        let G_c : SimpleGraph (Fin N) := SimpleGraph.fromRel (fun u v => u ≠ v ∧ χ (Sym2.mk (u, v)) = c)
        ¬ ContainsKk G_c S k

/--
`R(n; k, r)` is the smallest `N` satisfying `Prop129`.
-/
noncomputable def R (n k r : ℕ) : ℕ :=
  sInf { N | Prop129 N n k r }

/--
Erdős and Gyárfás conjectured that there is a constant $C > 1$ such that $R(n; 3, r) < C^{\sqrt{n}}$.
This is false as pointed out by Antonio Girao, $R(n; 3, 2)$ grows exponentially.
-/
@[category research solved, AMS 05]
theorem erdos_129 :
    answer(False) ↔ ∃ C : ℝ, C > 1 ∧ ∀ r, ∀ n ≥ 3, (R n 3 r : ℝ) < C ^ Real.sqrt n := by
  sorry
end Erdos129
