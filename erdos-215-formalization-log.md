# Erdős Problem 215 Formalization Log

## Problem Statement

Does there exist $S\subseteq \mathbb{R}^2$ such that every set congruent to $S$ (that is, $S$ after some translation and rotation) contains exactly one point from $\mathbb{Z}^2$?

## Discovery and Analysis

- A set $S \subset \mathbb{R}^2$ with this property is called a "Steinhaus set".
- The question was originally posed by Steinhaus.
- Erdős suspected that no such set exists.
- Jackson and Mauldin (2002) proved that a Steinhaus set does exist, using the Axiom of Choice.

## Formalization Plan

- Define the lattice $\mathbb{Z}^2$ in $\mathbb{R}^2$.
- Define congruent copies using isometric maps `≃ᵢ`.
- Define the property that a set intersects the lattice exactly once.
- State the theorem that such a set exists.

## Lean Implementation Details

- Used `ℝ × ℝ` for the plane.
- Used `∃! p` for "exactly one point".
- Included reference [JaMa02].

## Verification Results

- Verified with `lake build FormalConjectures/ErdosProblems/215.lean`.
