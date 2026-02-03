# Erdos Problem 147 Formalization Log

## Problem Description

Erdos Problem 147 asks if for every bipartite graph $H$ with min degree $r$, $ex(n, H) \gg n^{2 - 1/(r-1) + \epsilon}$.
Conjecture: Yes.

## Formalization Details

- **File Location:** `FormalConjectures/ErdosProblems/147.lean`
- **Theorem Name:** `Erdos147.erdos_147`
- **Status:** Disproved (Janzer).

We defined:
- `IsSubgraph`
- `TuranNumber`
- `MinDegree`

The theorem states the conjecture is false.

## References

- [Ja23] Janzer, O., "The extremal number of bipartite graphs with high minimum degree", arXiv:2302.05537 (2023).
- [Ja23b] Janzer, O., "personal communication".
