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
# Erdős Problem 1050

Irrationality of a series.

PROVED

STATUS: SOLVED

*Reference:* [erdosproblems.com/1050](https://www.erdosproblems.com/1050)
-/

open Finset

open scoped Topology Real

namespace Erdos1050

/-- English version: Series with exponential denominator is irrational -/@[category research solved, AMS 11]
theorem series_irrationality :
    Irrational (∑' n : ℕ+, (1 : ℝ) / (2^(n : ℝ) - 3)) := by
  sorry

end Erdos1050
