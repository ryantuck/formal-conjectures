/-
Copyright (c) 2025 Formal Conjectures. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

/-!
# Erdős Problem 505: Borsuk's Conjecture

Can every set of diameter 1 in ℝⁿ be partitioned into at most n+1 sets of diameter < 1?

## Status
DISPROVED - Kahn & Kalai (1993) for n ≥ 2015
Current smallest counterexample: n=64 (Brouwer & Jenrich, 2014)

True for n ≤ 3 but false for large n.
-/

namespace Erdos505

noncomputable axiom partitionNumber (n : ℕ) : ℕ

theorem borsuk_false_large_n :
    ∃ (N : ℕ), ∀ (n : ℕ), n ≥ N →
      partitionNumber n > n + 1 := by
  sorry

theorem borsuk_lower_bound (n : ℕ) (hn : n > 64) :
    (partitionNumber n : ℝ) ≥ (1.2 : ℝ) ^ Real.sqrt n := by
  sorry

end Erdos505
