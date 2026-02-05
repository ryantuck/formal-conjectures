/-
Copyright (c) 2025 Formal Conjectures. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic
import Mathlib.Algebra.Polynomial.Basic

/-!
# Erdős Problem 485: Minimum Terms in Polynomial Squares

Let f(k) be the minimum number of terms in P(x)², where P ∈ ℚ[x] ranges over all polynomials with
exactly k non-zero terms.

**Question:** Is it true that f(k) → ∞ as k → ∞?

## Status
PROVED - Schinzel showed f(k) > log log k / log 2, and Schinzel-Zannier improved this to
f(k) ≫ log k.

Erdős established that f(k) < k^(1-c) for some constant c > 0.

## References
- Erdős and Rényi (conjecture)
- Schinzel (first bound)
- Schinzel and Zannier (improved bound)
- Halberstam, Problem 4.4
-/

namespace Erdos485

open Polynomial

/-- Count of non-zero terms in a polynomial -/
noncomputable def termCount {R : Type*} [Semiring R] (P : R[X]) : ℕ :=
  P.support.card

/-- f(k) is the minimum number of terms in P² for polynomials P with exactly k terms -/
noncomputable def minSquareTerms (k : ℕ) : ℕ :=
  sInf { n | ∃ (P : ℚ[X]), termCount P = k ∧ termCount (P^2) = n }

/-- Main conjecture (PROVED): f(k) → ∞ as k → ∞ -/
theorem minSquareTerms_diverges :
    Filter.Tendsto minSquareTerms Filter.atTop Filter.atTop := by
  sorry

/-- Schinzel's initial bound: f(k) > log log k / log 2 -/
theorem schinzel_bound (k : ℕ) (hk : k ≥ 2) :
    (minSquareTerms k : ℝ) > Real.log (Real.log k) / Real.log 2 := by
  sorry

/-- Schinzel-Zannier improved bound: f(k) ≫ log k -/
theorem schinzel_zannier_bound :
    ∃ (c : ℝ) (hc : c > 0),
      ∀ᶠ (k : ℕ) in Filter.atTop,
        (minSquareTerms k : ℝ) ≥ c * Real.log k := by
  sorry

/-- Erdős upper bound: f(k) < k^(1-c) for some constant c > 0 -/
theorem erdos_upper_bound :
    ∃ (c : ℝ) (hc : 0 < c ∧ c < 1),
      ∀ᶠ (k : ℕ) in Filter.atTop,
        (minSquareTerms k : ℝ) < (k : ℝ)^(1 - c) := by
  sorry

end Erdos485
