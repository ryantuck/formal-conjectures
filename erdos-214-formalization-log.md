# Erdős Problem 214 Formalization Log

## Problem Statement

Let $S\subset \mathbb{R}^2$ be such that no two points in $S$ are distance $1$ apart. Must the complement of $S$ contain four points which form a unit square?

## Discovery and Analysis

- The problem is about sets avoiding the unit distance.
- If $S$ avoids distance 1, does $S^c$ contain a unit square?
- Juhász (1979) proved a much stronger result: the complement of any set avoiding distance 1 contains a congruent copy of *any* four points.
- This is false for large sets of points (e.g. if the measure of $S$ is large, it can avoid large patterns).

## Formalization Plan

- Define the property `AvoidsDistanceOne` for a set in $\mathbb{R}^2$.
- Define `ContainsUnitSquare` as the existence of four points with the appropriate side and diagonal lengths.
- State the theorem for the unit square case.
- State the variant for the general case of any four points using isometric maps `≃ᵢ`.

## Lean Implementation Details

- Used `ℝ × ℝ` for the plane.
- Used `Metric.dist` for distances.
- Used `≃ᵢ` (isometric equivalence) for congruent copies.
- Included reference [Ju79].

## Verification Results

- Verified with `lake build FormalConjectures/ErdosProblems/214.lean`.
