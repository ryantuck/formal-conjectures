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
import FormalConjecturesForMathlib.Data.Set.Density

/-!
# Erdős Problem 37

*Reference:* [erdosproblems.com/37](https://www.erdosproblems.com/37)
-/

namespace Erdos37

open scoped BigOperators Pointwise

/--
Schnirelmann density of a set `A`.
-/
noncomputable def schnirelmannDensity (A : Set ℕ) : ℝ :=
  sInf {((A ∩ Finset.Icc 1 n).ncard : ℝ) / n | n : ℕ}

/--
A set `A` is an essential component if for every `B` with $0 < d_s(B) < 1$, we have $d_s(A+B) > d_s(B)$.
-/
def IsEssentialComponent (A : Set ℕ) : Prop :=
  ∀ B : Set ℕ, 0 < schnirelmannDensity B → schnirelmannDensity B < 1 →
    schnirelmannDensity (A + B) > schnirelmannDensity B

/--
A set `A` is lacunary if its elements grow geometrically.
-/
def IsLacunary (A : Set ℕ) : Prop :=
  ∃ (seq : ℕ → ℕ), StrictMono seq ∧ Set.range seq = A ∧ ∃ r > 1, ∀ n, (seq (n + 1) : ℝ) ≥ r * seq n

/--
Can a lacunary set be an essential component?

The answer is no, proved by Ruzsa [Ru87].

[Ru87] I. Z. Ruzsa, _Essential components_, Proc. London Math. Soc. (3) 54 (1987), 38–56.
-/
@[category research solved, AMS 11]
theorem erdos_37 : answer(False) ↔ ∃ A : Set ℕ, IsLacunary A ∧ IsEssentialComponent A := by
  sorry

end Erdos37
