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
# Erdős Problem 187

*Reference:* [erdosproblems.com/187](https://www.erdosproblems.com/187)

Find the best function $f(d)$ such that, in any 2-colouring of the integers, at least one colour
class contains an arithmetic progression with common difference $d$ of length $f(d)$ for
infinitely many $d$.
-/

namespace Erdos187

open Real Classical

/--
A set A contains an arithmetic progression with common difference d and length k.
-/
def ContainsAP (A : Set ℤ) (d k : ℕ) : Prop :=
  ∃ a : ℤ, ∀ i : ℕ, i < k → a + i * (d : ℤ) ∈ A

/--
In any 2-colouring of ℤ, at least one colour class contains an arithmetic progression
with common difference d and length f(d) for infinitely many d.
-/
def IsValidLowerBound (f : ℕ → ℕ) : Prop :=
  ∀ (c : ℤ → Fin 2), ∃ (i : Fin 2),
    { d : ℕ | ContainsAP { n | c n = i } d (f d) }.Infinite

/--
Erdős asked for the best function f(d) such that IsValidLowerBound(f) holds.
Beck [Be80] showed that there is a colouring such that f(d) ≤ (1+o(1)) log2 d.
-/
@[category research open, AMS 05 11]
theorem erdos_187 :
    ∃ (f : ℕ → ℕ), IsValidLowerBound f ∧ ∀ (ε : ℝ), ε > 0 →
    ¬ IsValidLowerBound (fun d ↦ Nat.ceil ((1 + ε) * log d / log 2)) := by
  sorry

end Erdos187
