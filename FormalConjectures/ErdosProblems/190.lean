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
# Erdős Problem 190

*Reference:* [erdosproblems.com/190](https://www.erdosproblems.com/190)

Let $H(k)$ be the smallest $N$ such that in any finite colouring of $\{1,\ldots,N\}$ (into any
number of colours) there is always either a monochromatic $k$-term arithmetic progression or
a rainbow arithmetic progression (i.e. all elements are different colours). Estimate $H(k)$.
Is it true that
$$ H(k)^{1/k}/k 	o \infty $$
as $k	o\infty$?
-/

namespace Erdos190

open Finset Real Classical

/--
A set is a k-term arithmetic progression.
-/
def IsAP (P : Finset ℕ) (k : ℕ) : Prop :=
  ∃ (a d : ℕ), d > 0 ∧ P = image (fun i => a + i * d) (range k)

/--
A set is monochromatic under coloring c.
-/
def IsMonochromatic {α : Type} (P : Finset ℕ) (c : ℕ → α) : Prop :=
  ∃ color, ∀ x ∈ P, c x = color

/--
A set is rainbow under coloring c.
-/
def IsRainbow {α : Type} (P : Finset ℕ) (c : ℕ → α) : Prop :=
  Set.InjOn c P

/--
H(k) is the smallest N such that any finite colouring of {1, ..., N} contains
either a monochromatic k-term AP or a rainbow k-term AP.
-/
noncomputable def H (k : ℕ) : ℕ :=
  sInf { N | ∀ (C : Type) [Fintype C] (col : ℕ → C),
    ∃ (P : Finset ℕ), P ⊆ Icc 1 N ∧ IsAP P k ∧ (IsMonochromatic P col ∨ IsRainbow P col) }

/--
Erdős asked if $H(k)^{1/k} / k 	o \infty$ as $k 	o \infty$.
-/
@[category research open, AMS 05 11]
theorem erdos_190 :
    Filter.Tendsto (fun k ↦ (H k : ℝ) ^ (1 / k : ℝ) / k) Filter.atTop Filter.atTop := by
  sorry

end Erdos190
