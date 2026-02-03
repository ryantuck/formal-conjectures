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
import Mathlib.SetTheory.Ordinal.Arithmetic

/-!
# Erdős Problem 118

*Reference:* [erdosproblems.com/118](https://www.erdos.com/118)
-/

namespace Erdos118

open Ordinal Relation

/--
A coloring of pairs of elements of a type `α` with 2 colors.
-/  
def Coloring (α : Type*) := α → α → Bool

/--
A subset `S` is homogeneous for color `c` if all distinct pairs in `S` have color `c`.
-/  
def IsHomogeneous (α : Type*) (C : Coloring α) (S : Set α) (c : Bool) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x ≠ y → C x y = c

/--
The arrow notation $\alpha \to (\beta, \gamma)^2$.
For every 2-coloring of pairs of $\alpha$, there is a homogeneous set of type $\beta$ in color 0
or a homogeneous set of type $\gamma$ in color 1.
We interpret "set of type $\beta$" as the existence of an order-embedding from $\beta$ into the set.
-/
def Arrow (α β γ : Ordinal) : Prop :=
  ∀ (C : Coloring α.out.α),
    (∃ (f : β.out.r ↪r α.out.r), IsHomogeneous α.out.α C (Set.range f) false) ∨
    (∃ (f : γ.out.r ↪r α.out.r), IsHomogeneous α.out.α C (Set.range f) true)
/--
Erdős and Hajnal conjectured that if $\alpha \to (\alpha, 3)^2$, then $\alpha \to (\alpha, n)^2$
for every finite $n$.

Schipperus [Sc99] and Darby [Da99] independently proved this is false.
Larson [La00] showed a counterexample with $\alpha = \omega^{\omega^2}$ and $n=5$.
-/  
@[category research solved, AMS 03 05]
theorem erdos_118 :
    answer(False) ↔ ∀ (α : Ordinal), Arrow α α 3 → ∀ (n : ℕ), Arrow α α n :=
  sorry

end Erdos118
