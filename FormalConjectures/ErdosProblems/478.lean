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
# Erdős Problem 478

Let p be a prime and define Aₚ = {k! mod p : 1 ≤ k < p}.
Is it true that |Aₚ| ~ (1 - 1/e)·p?

Lower bound: |Aₚ| ≥ (√2 - o(1))·p^(1/2) (Grebennikov et al).
Wilson's theorem: |Aₚ| ≤ p - 2.
Question: Is |Aₚ| < p - 2 always? (Verified for p < 10⁹)

*Reference:* [erdosproblems.com/478](https://www.erdosproblems.com/478)
-/

open Filter Topology BigOperators Real Classical

namespace Erdos478

/-- Aₚ is the set of factorial residues -/
def A_p (p : ℕ) : Finset (ZMod p) :=
  ((Finset.range (p - 1)).image (fun k => ((k + 1).factorial : ZMod p))).filter (· ≠ 0)

/-- Main conjecture: |Aₚ| ~ (1 - 1/e)·p -/
@[category research open, AMS 11]
theorem erdos_478_conjecture :
    Tendsto (fun p : {p : ℕ // p.Prime} => ((A_p p : Finset (ZMod p)).card : ℝ) / p)
      atTop (𝓝 (1 - Real.exp (-1))) := by
  sorry

/-- Lower bound -/
@[category research open, AMS 11]
theorem erdos_478_lower :
    ∀ᶠ p : {p : ℕ // p.Prime} in atTop,
      ((A_p p : Finset (ZMod p)).card : ℝ) ≥ (Real.sqrt 2 - 0.1) * p ^ ((1:ℝ)/2) := by
  sorry

end Erdos478
