# Erdős Problem 210 Formalization Log

## Problem Statement

Let $f(n)$ be minimal such that the following holds. For any $n$ points in $\mathbb{R}^2$, not all on a line, there must be at least $f(n)$ many lines which contain exactly 2 points (called 'ordinary lines'). Does $f(n)	o \infty$? How fast?

## Discovery and Analysis

- The Sylvester-Gallai theorem (1944) states that for any finite set of points not all collinear, there exists at least one ordinary line (so $f(n) \ge 1$).
- Motzkin (1951) proved $f(n) 	o \infty$.
- Kelly and Moser (1958) proved $f(n) \ge 3n/7$.
- Csima and Sawyer (1993) proved $f(n) \ge 6n/13$ for $n \ge 8$.
- Green and Tao (2013) proved the Dirac-Motzkin conjecture for large $n$: $f(n) \ge n/2$ for even $n$, and $f(n) \ge 3\lfloor n/4 floor$ for odd $n$.

## Formalization Plan

- Define collinearity for sets in $\mathbb{R}^2$.
- Define the set of lines determined by a finite set of points.
- Define ordinary lines as those containing exactly 2 points.
- Define $f(n)$ as the infimum of the number of ordinary lines.
- State the Green-Tao result as the theorem.

## Lean Implementation Details

- Used `ℝ × ℝ` for points in the plane.
- Used `Set.ncard` for counting lines (the set of lines determined by a finite set is finite).
- `∀ᶠ n in atTop` for large $n$.
- Included reference [GrTa13].

## Verification Results

- Verified with `lake build FormalConjectures/ErdosProblems/210.lean`.
