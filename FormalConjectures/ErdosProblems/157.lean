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
# Erdős Problem 157

*Reference:* [erdosproblems.com/157](https://www.erdosproblems.com/157)
-/

namespace Erdos157

/--
Does there exist an infinite Sidon set which is an asymptotic basis of order 3?

This problem has been solved in the affirmative by Pilatte [Pi23].

[ESS94] P. Erdős, A. Sárközy, and V. T. Sós, "On sumsets of Sidon sets. I", J. Number Theory 47 (1994), 329–347.
[Pi23] C. Pilatte, "Sidon sets that are asymptotic bases", arXiv:2310.12876, 2023.
-/
@[category research solved, AMS 11]
theorem erdos_157 : answer(True) ↔ ∃ A : Set ℕ, A.Infinite ∧ IsSidon A ∧ A.IsAsymptoticAddBasisOfOrder 3 := by
  sorry

end Erdos157
