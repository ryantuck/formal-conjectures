# Erdős Problem 193 Formalization Log

## Problem Statement

Let $S\subseteq \mathbb{Z}^3$ be a finite set and let $A=\{a_1,a_2,\ldots,\}\subset \mathbb{Z}^3$ be an infinite $S$-walk, so that $a_{i+1}-a_i\in S$ for all $i$. Must $A$ contain three collinear points?

## Discovery and Analysis

- The problem asks whether every infinite walk in $\mathbb{Z}^3$ with steps from a finite set $S$ must have at least three points on some line.
- Gerver and Ramsey (1979) proved that for any such walk in $\mathbb{Z}^2$, the answer is YES (there must be 3 collinear points).
- For $\mathbb{Z}^3$, they proved that for any finite $S$ and an infinite $S$-walk $A$, the number of collinear points is bounded by some constant $K(S)$.
- The question of whether $K(S)$ can be 2 (meaning no 3 points are collinear) remains open for $\mathbb{Z}^3$.
- Collinearity in $\mathbb{R}^3$ for points $p, q, r$ can be defined using the `collinear` predicate in Mathlib.
- An $S$-walk is defined as a sequence $A : \mathbb{N} 	o \mathbb{Z}^3$ such that $A(n+1) - A(n) \in S$ for all $n$.
- If the walk is not injective (i.e., $a_i = a_j$ for some $i 
e j$), then for any $k$, the points $a_i, a_j, a_k$ are collinear (since two points on a line plus a duplicate are still on the line).
- Thus, the non-trivial case is for self-avoiding walks.

## Formalization Plan

- Use `Fin 3 → ℤ` to represent $\mathbb{Z}^3$.
- Define the $S$-walk condition: `∀ n, A (n + 1) - A n ∈ S`.
- Define the three collinear points condition: `∃ i j k, i < j ∧ j < k ∧ collinear ℝ { (A i : Fin 3 → ℝ), (A j : Fin 3 → ℝ), (A k : Fin 3 → ℝ) }`.
- State the conjecture as a property of all such walks in $\mathbb{Z}^3$.

## Lean Implementation Details

- Import `Mathlib.Geometry.Euclidean.Collinear` for collinearity.
- Use `Fin 3 → ℤ` for the points.
- The theorem will be marked as `research open`.

## Verification Results

- To be verified with `lake build`.
