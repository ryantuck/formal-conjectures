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
# Erdős Problem 231

*Reference:* [erdosproblems.com/231](https://www.erdosproblems.com/231)
-/

namespace Erdos231

/--
An abelian square is two consecutive blocks x and y where y is a permutation of x.
-/
def IsAbelianSquare {α : Type*} [DecidableEq α] (s : List α) (i : ℕ) (len : ℕ) : Prop :=
  let block := (s.drop i).take (2 * len)
  let x := block.take len
  let y := block.drop len
  x.length = len ∧ y.length = len ∧
  ∀ a, x.count a = y.count a

/--
A string contains an abelian square.
-/
def ContainsAbelianSquare {α : Type*} [DecidableEq α] (s : List α) : Prop :=
  ∃ i len, len > 0 ∧ IsAbelianSquare s i len

/--
Let $S$ be a string of length $2^k-1$ formed from an alphabet of $k$ characters.
Must $S$ contain an abelian square?

Erdős initially conjectured yes for all $k\geq 2$, but for $k=4$ this was
disproved by de Bruijn and Erdős. The existence of infinite abelian-square-free
strings over 4-letter alphabets was proven by Keränen [Ke92].

[Ke92] Keränen, V., _Abelian squares are avoidable on 4 letters_.
  ICALP 1992, Lecture Notes in Computer Science vol 623 (1992), 41-52.
-/
@[category research solved, AMS 68]
theorem erdos_231 : ¬ ∀ k : ℕ, k ≥ 2 →
    ∀ alphabet : Finset ℕ, alphabet.card = k →
    ∀ s : List ℕ, s.length = 2^k - 1 →
    (∀ c ∈ s, c ∈ alphabet) →
    ContainsAbelianSquare s := by
  sorry

/--
There exists an infinite string over a 4-letter alphabet with no abelian squares.
-/
@[category research solved, AMS 68]
theorem erdos_231.keranen : ∃ f : ℕ → Fin 4,
    ∀ i len, len > 0 → ¬ IsAbelianSquare (List.ofFn (fun n : Fin (i + 2 * len) => f n)) i len := by
  sorry

end Erdos231
