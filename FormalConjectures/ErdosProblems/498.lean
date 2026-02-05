/-
Copyright (c) 2025 Formal Conjectures. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

/-!
# Erdős Problem 498: Complex Number Sums

For complex numbers z₁,...,zₙ with |zᵢ| ≥ 1, does any disc of radius 1 contain at most C(n,⌊n/2⌋)
sums Σεᵢzᵢ (with εᵢ ∈ {-1,1})?

## Status
PROVED - Erdős (1945), Kleitman (1965, 1970)

Related to Problem 395.
-/

namespace Erdos498

noncomputable def signedSum {n : ℕ} (z : Fin n → ℂ) (signs : Fin n → ℤ) : ℂ :=
  ∑ i, (signs i : ℂ) * z i

noncomputable def discSums {n : ℕ} (z : Fin n → ℂ) (center radius : ℂ) : Set ℂ :=
  { s | ∃ (signs : Fin n → ℤ), (∀ i, signs i = -1 ∨ signs i = 1) ∧
    s = signedSum z signs }

theorem bounded_disc_sums (n : ℕ) (z : Fin n → ℂ) (hz : ∀ i, Complex.abs (z i) ≥ 1) :
    (discSums z 0 1).ncard ≤ Nat.choose n (n / 2) := by
  sorry

end Erdos498
