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
# Erdős Problem 595

Is there an infinite graph G that contains no K₄ and cannot be expressed as the union
of countably many triangle-free graphs?

OPEN

*Reference:* [erdosproblems.com/595](https://www.erdosproblems.com/595)
-/

open SimpleGraph Cardinal

open scoped Topology Real

namespace Erdos595

variable {α : Type*}

/-- A graph is triangle-free if it contains no K₃ -/
def IsTriangleFree (G : SimpleGraph α) : Prop :=
  ∀ (a b c : α), G.Adj a b → G.Adj b c → G.Adj c a → False

/-- ∃ infinite K₄-free graph not union of countably many triangle-free graphs -/
@[category research open, AMS 03 05]
theorem infinite_k4_free_not_countable_union_triangle_free (answer : Prop) :
    answer ↔ ∃ (G : SimpleGraph ℕ),
      (Infinite ℕ) ∧
      (∀ (f : Fin 4 ↪ ℕ), ¬ ∀ i j, i ≠ j → G.Adj (f i) (f j)) ∧
      (¬ ∃ (family : ℕ → SimpleGraph ℕ),
        (∀ n, IsTriangleFree (family n)) ∧
        (∀ v w, G.Adj v w → ∃ n, (family n).Adj v w)) := by
  sorry

end Erdos595
