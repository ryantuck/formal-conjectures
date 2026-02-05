/-
Copyright (c) 2025 Formal Conjectures. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

/-!
# Erdős Problem 491: Additive Functions and Logarithm

Let f: ℕ → ℝ be an additive function (where f(ab) = f(a) + f(b) when gcd(a,b) = 1).
If |f(n+1) - f(n)| < c for all n, must there exist c' where f(n) = c' log n + O(1)?

## Status
PROVED - Wirsing (1970)

Erdős previously showed the statement holds under stronger conditions: f(n+1) - f(n) = o(1)
or f(n+1) ≥ f(n).
-/

namespace Erdos491

noncomputable axiom additiveFunction (f : ℕ → ℝ) : Prop

theorem wirsing_bound (f : ℕ → ℝ) (h_add : additiveFunction f)
    (h_bounded : ∃ (c : ℝ), ∀ n, |f (n+1) - f n| < c) :
    ∃ (c' : ℝ), ∀ᶠ n in Filter.atTop,
      |f n - c' * Real.log n| < 1 := by
  sorry

end Erdos491
