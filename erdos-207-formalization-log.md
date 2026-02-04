# Erdős Problem 207 Formalization Log

## Problem Statement

For any $g\geq 2$, if $n$ is sufficiently large and $\equiv 1,3\pmod{6}$ then there exists a 3-uniform hypergraph on $n$ vertices such that
- every pair of vertices is contained in exactly one edge (i.e. the graph is a Steiner triple system) and
- for any $2\leq j\leq g$ any collection of $j$ edges contains at least $j+3$ vertices.

## Discovery and Analysis

- A Steiner triple system (STS) is a decomposition of the edges of $K_n$ into triangles.
- It is well known that an STS exists if and only if $n \equiv 1, 3 \pmod 6$.
- The condition that $j$ edges contain at least $j+3$ vertices is a "sparsity" or "high girth" condition.
- For $j=2$, we have $|e_1 \cup e_2| = 3 + 3 - |e_1 \cap e_2|$. Since any two vertices are in exactly one edge, $|e_1 \cap e_2| \le 1$, so $|e_1 \cup e_2| \ge 5 = 2 + 3$. This is always true for an STS.
- The Erdős-Heilbronn conjecture (or related problems) asked for the existence of such systems for any $g$.
- Proved in 2022 by Kwan, Sah, Sawhney, and Simkin.

## Formalization Plan

- Define a `Hypergraph` structure.
- Define `IsSteinerTripleSystem` as a predicate on hypergraphs.
- Define `IsSparse` for the condition on $j$ edges.
- State the theorem for sufficiently large $n$ with the congruence condition.

## Lean Implementation Details

- Used `Finset.sup id` for the union of a collection of finsets.
- Used `∀ᶠ n in atTop` for "sufficiently large $n$".
- Included the reference [KSSS22b].

## Verification Results

- Verified with `lake build FormalConjectures/ErdosProblems/207.lean`.
