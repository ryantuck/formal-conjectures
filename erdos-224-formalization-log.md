# Erdős Problem 224 - Formalization Log

## Problem Statement

If $A\subseteq \mathbb{R}^d$ is any set of $2^d+1$ points, must some three points in $A$ determine an obtuse angle?

## Status

**PROVED** (Yes) - Verified in Lean

## Key Results

- **General case**: Proved by Danzer and Grünbaum [DaGr62]
- **d=2**: Trivial
- **d=3**: Unpublished proof by Kuiper and Boerdijk
- **Sharpness**: The bound $2^d + 1$ is sharp - the vertices of a $d$-dimensional cube ($2^d$ points) contain no obtuse angles

## Formalization Details

### Main Components

1. **`IsObtuse a b c`**: The angle $\angle abc$ is obtuse if it exceeds $\pi/2$

2. **Main theorem `erdos_224`**: Any set of $2^d + 1$ points in $\mathbb{R}^d$ contains an obtuse angle

3. **`erdos_224.sharp`**: The bound is tight - there exist sets of $2^d$ points with no obtuse angles

## References

- [DaGr62] Danzer, L. and Grünbaum, B., _Über zwei Probleme bezüglich konvexer Körper von P. Erdős und von V. L. Klee_. Math. Z. (1962), 214-230.

## Build Status

✅ Successfully built with `lake build FormalConjectures/ErdosProblems/224.lean`
