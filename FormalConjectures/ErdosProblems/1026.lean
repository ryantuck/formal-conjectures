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
# Erdős Problem 1026

Maximum monotonic subsequences.

SOLVED

STATUS: SOLVED

*Reference:* [erdosproblems.com/1026](https://www.erdosproblems.com/1026)
-/

open Finset Filter

open scoped Topology Real

namespace Erdos1026

/-- English version: Maximum constant for monotonic subsequence sum -/@[category research solved, AMS 05]
theorem monotonic_subsequence_constant :
    ∃ (c : ℝ), 0 < c ∧
      ∀ (seq : ℕ → ℝ) (n : ℕ),
        ∃ (subseq : Finset ℕ),
          (Monotone (fun i => seq i) ∨ Antitone (fun i => seq i)) →
          c / Real.sqrt n * (Finset.range n).sum seq ≤ subseq.sum seq := by
  sorry

end Erdos1026
