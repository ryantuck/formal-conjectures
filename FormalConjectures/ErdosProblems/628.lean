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
# Erdős Problem 628

Given a graph G with chromatic number k that contains no K_k, must G contain two
vertex-disjoint subgraphs with chromatic numbers at least a and b respectively,
whenever a, b ≥ 2 and a + b = k + 1?

OPEN

*Reference:* [erdosproblems.com/628](https://www.erdosproblems.com/628)
-/

open SimpleGraph

open scoped Topology Real

namespace Erdos628

variable {α : Type*}

/-- Chromatic number -/
noncomputable def chromaticNumber (G : SimpleGraph α) : ℕ := sorry

/-- (a,b)-splittable: has two disjoint subgraphs with χ ≥ a and χ ≥ b -/
def IsSplittable (a b : ℕ) (G : SimpleGraph α) : Prop := sorry

/-- K_k-free graph with χ = k is (a,b)-splittable for a + b = k + 1 -/
@[category research open, AMS 05]
theorem chromatic_k_is_splittable (k a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hsum : a + b = k + 1)
    (G : SimpleGraph α) (hχ : chromaticNumber G = k)
    (hfree : ∀ (f : Fin k ↪ α), ¬ ∀ i j, i ≠ j → G.Adj (f i) (f j)) :
    IsSplittable a b G := by
  sorry

end Erdos628
