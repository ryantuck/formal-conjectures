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
# Erdős Problem 1017

Clique partition of graphs.

OPEN

STATUS: OPEN

*Reference:* [erdosproblems.com/1017](https://www.erdosproblems.com/1017)
-/

open Finset Filter

open scoped Topology Real

namespace Erdos1017

variable {α : Type*}

/--
English version: The minimum number of complete graphs that partition the edges of `G`. -/
noncomputable def cliquePartitionSize (G : SimpleGraph α) : ℕ∞ :=
  open scoped Classical in
  iInf (fun (P : Set (Set α)) =>
    if (∀ s ∈ P, G.IsClique s) ∧ (∀ e ∈ G.edgeSet, ∃! s ∈ P, ∀ x ∈ e, x ∈ s) then
      Set.encard P
    else ⊤)

/--
English version: The maximum clique partition size over all graphs with `n` vertices and `k` edges. -/
noncomputable def f (n k : ℕ) : ℕ∞ :=
  open scoped Classical in
  iSup (fun (G : SimpleGraph (Fin n)) =>
    if G.edgeFinset.card = k then cliquePartitionSize G else 0)

/--
English version:  -/
@[category research open, AMS 05]
theorem clique_partition_estimate : answer(sorry) ↔
    ∃ (g : ℕ → ℕ → ℝ),
      ∀ k_func : ℕ → ℕ, (∀ n, k_func n > n^2 / 4) →
        Filter.Tendsto (fun (n : ℕ) => (f n (k_func n)).toNat / g n (k_func n)) Filter.atTop (nhds 1) := by
  sorry

end Erdos1017
