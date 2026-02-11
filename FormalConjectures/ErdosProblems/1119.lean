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
# Erdős Problem 1119

Cardinality of families of entire functions.

SOLVED

*Reference:* [erdosproblems.com/1119](https://www.erdosproblems.com/1119)
-/

open Finset

open scoped Real

namespace Erdos1119

/-- If F is a family of entire functions such that for every z₀ ∈ ℂ,
    the set {f(z₀) : f ∈ F} has cardinality ≤ 𝔪, then |F| ≤ 𝔪.
    This holds when 𝔪⁺ < 𝔠 (Hales 1974). -/
@[category research solved, AMS 30]
theorem cardinality_entire_function_families
    (𝔪 : Cardinal) (h1 : Cardinal.aleph 0 < 𝔪)
    (h2 : 𝔪 < Cardinal.continuum)
    (h3 : Order.succ 𝔪 < Cardinal.continuum) :
    ∀ (F : Set (ℂ → ℂ)),
      (∀ f ∈ F, Differentiable ℂ f) →
      (∀ z₀ : ℂ, Cardinal.mk {c : ℂ | ∃ f ∈ F, f z₀ = c} ≤ 𝔪) →
      Cardinal.mk F ≤ 𝔪 := by
  sorry

end Erdos1119
