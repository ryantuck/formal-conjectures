# Erdos Problem 146 Formalization Log

## Problem Description

Erdos Problem 146 asks for the Turán number $ex(n, H)$ where $H$ is a bipartite, $r$-degenerate graph.
Conjecture: $ex(n, H) = O(n^{2-1/r})$.

## Formalization Details

- **File Location:** `FormalConjectures/ErdosProblems/146.lean`
- **Theorem Name:** `Erdos146.erdos_146`
- **Status:** Open.

We defined:
- `IsDegenerate`
- `IsSubgraph`
- `TuranNumber` (noncomputable)

The theorem states the conjectured bound.

## References

- [ErSi84] Erdős, P. and Simonovits, M., "Cube-supersaturated graphs and related problems", Progress in Graph Theory (1984), 229-246.
