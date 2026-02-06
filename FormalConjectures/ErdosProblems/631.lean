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
# Erdős Problem 631

Does every planar graph have list chromatic number χ_L(G) ≤ 5?

PROVED by Thomassen; tight bound shown by Voigt

*Reference:* [erdosproblems.com/631](https://www.erdosproblems.com/631)
-/

open SimpleGraph

open scoped Topology Real

namespace Erdos631

variable {α : Type*}

/-- List chromatic number -/
noncomputable def listChromaticNumber (G : SimpleGraph α) : ℕ := sorry

/-- A graph is planar -/
def IsPlanar (G : SimpleGraph α) : Prop := sorry

/-- Every planar graph has χ_L(G) ≤ 5 -/
@[category research solved, AMS 05]
theorem planar_list_chromatic (G : SimpleGraph α) (hplanar : IsPlanar G) :
    listChromaticNumber G ≤ 5 := by
  sorry

end Erdos631
