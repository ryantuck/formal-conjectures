# Erdős Problem 209 Formalization Log

## Problem Statement

Let $A$ be a finite collection of $d\geq 4$ non-parallel lines in $\mathbb{R}^2$ such that there are no points where at least four lines from $A$ meet. Must there exist a 'Gallai triangle' (or 'ordinary triangle'): three lines from $A$ which intersect in three points, and each of these intersection points only intersects two lines from $A$?

## Discovery and Analysis

- An ordinary point of an arrangement of lines is a point where exactly two lines meet.
- An ordinary triangle is a triangle formed by three lines of the arrangement whose vertices are all ordinary points.
- The Sylvester-Gallai theorem states that any arrangement of lines (not all concurrent) has at least one ordinary point.
- The conjecture was that any arrangement with no 4-concurrent points has at least one ordinary triangle.
- Füredi and Palásti (1984) showed this is false for $d$ not divisible by 9.
- Escudero (2016) showed this is false for all $d \ge 4$.

## Formalization Plan

- Define a `Line` structure in $\mathbb{R}^2$.
- Define an `Arrangement` of non-parallel lines.
- Define `multiplicity` of a point in an arrangement.
- Define `IsOrdinaryPoint` and `IsOrdinaryTriangle`.
- State the theorem with `answer(False)` citing Escudero.

## Lean Implementation Details

- Used `ℝ × ℝ` for points.
- Used `Finset Line` for the arrangement.
- `IsOrdinaryTriangle` explicitly requires 3 distinct points and each being ordinary.

## Verification Results

- Verified with `lake build FormalConjectures/ErdosProblems/209.lean`.
