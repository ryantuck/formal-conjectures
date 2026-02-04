# Erdős Problem 224 - Formalization Log

## Problem Statement

If $A \subseteq \mathbb{R}^d$ is any set of $2^d + 1$ points, must some three points in $A$ determine an obtuse angle?

## Status

**SOLVED** (Yes, this is true)

## Key Results

- Any set of $2^d + 1$ points in $\mathbb{R}^d$ contains three points forming an obtuse angle
- The bound $2^d + 1$ is sharp: the vertices of a $d$-dimensional cube (which number $2^d$) contain no obtuse angles

## Formalization Details

### Main Components

1. **`IsObtuse`**: An angle $\angle abc$ is obtuse if it is strictly greater than $\pi/2$

2. **Main theorem `erdos_224`**: Any set of $2^d + 1$ points in $\mathbb{R}^d$ contains an obtuse angle

3. **`erdos_224.sharp`**: The bound is sharp - there exists a set of $2^d$ points (the vertices of a $d$-cube) with no obtuse angles

## Technical Notes

- The formalization uses the `angle` function from Mathlib's Euclidean geometry library
- Points are represented as elements of `EuclideanSpace ℝ (Fin d)`

## Build Status

✅ Successfully built with `lake build FormalConjectures/ErdosProblems/224.lean`
