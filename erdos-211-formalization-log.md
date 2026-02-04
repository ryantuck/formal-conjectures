# Erdős Problem 211 Formalization Log

## Problem Statement

Let $1\leq k<n$. Given $n$ points in $\mathbb{R}^2$, at most $n-k$ on any line, there are $\gg kn$ many lines which contain at least two points.

## Discovery and Analysis

- This is a version of Beck's Theorem (or Szemerédi-Trotter type result).
- Beck (1983) and Szemerédi and Trotter (1983) independently proved that either a set of $n$ points has $\Omega(n)$ points on a line, or it determines $\Omega(n^2)$ lines.
- The statement "at most $n-k$ on any line $\implies \Omega(kn)$ lines" generalizes this.
- If $k=1$, it says if not all points are on a line, there are $\Omega(n)$ lines (which is true by Sylvester-Gallai and more).
- If $k=\epsilon n$, it says if at most $(1-\epsilon)n$ points are on a line, there are $\Omega(n^2)$ lines.

## Formalization Plan

- Define the set of lines determined by pairs of points from a finite set $P \subset \mathbb{R}^2$.
- Define the number of points on a line.
- State the theorem as the existence of a constant $C$ such that the number of lines is at least $C k n$.

## Lean Implementation Details

- Used `ℝ × ℝ` for points.
- Represented lines as sets of points `{p | ∃ t, p = (1-t)p1 + t p2}`.
- Used `Set.ncard` to count the number of lines.
- Used `classical` logic for point-line incidence decidability.
- Included references [Be83] and [SzTr83].

## Verification Results

- Verified with `lake build FormalConjectures/ErdosProblems/211.lean`.
